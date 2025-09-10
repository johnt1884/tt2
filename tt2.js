// ==UserScript==
// @name         Thread Tracker
// @namespace    http://tampermonkey.net/
// @version      2.8
// @description  Tracks OTK threads on /b/, stores messages and media, shows top bar with colors and controls, removes inactive threads entirely
// @match        https://boards.4chan.org/b/
// @grant        GM_xmlhttpRequest
// @grant        GM.getValue
// @grant        GM.setValue
// ==/UserScript==

(function() {
    'use strict';

    // --- IIFE Scope Helper for Intersection Observer ---
    function handleIntersection(entries, observerInstance) {
        entries.forEach(entry => {
            const wrapper = entry.target;
            let iframe = wrapper.querySelector('iframe');

            if (entry.isIntersecting) {
                // Element is now visible
                if (!iframe) {
                    // If the iframe was removed, recreate it
                    const newIframe = document.createElement('iframe');
                    // Copy attributes from a template or stored config if necessary
                    // For now, assuming basic recreation is enough
                    newIframe.style.position = 'absolute';
                    newIframe.style.top = '0';
                    newIframe.style.left = '0';
                    newIframe.style.width = '100%';
                    newIframe.style.height = '100%';
                    newIframe.setAttribute('frameborder', '0');
                    newIframe.setAttribute('allowfullscreen', 'true');
                    if (wrapper.classList.contains('otk-twitch-embed-wrapper')) {
                        newIframe.setAttribute('scrolling', 'no');
                    } else if (wrapper.classList.contains('otk-youtube-embed-wrapper')) {
                        newIframe.setAttribute('allow', 'accelerometer; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share');
                    }
                    newIframe.dataset.src = wrapper.dataset.embedUrl;
                    wrapper.innerHTML = '';
        if (window.twttr?.widgets?.load) {
            twttr.widgets.load(wrapper);
        } // Clear placeholder
                    wrapper.appendChild(newIframe);
                    iframe = newIframe;
                }

                if (iframe && iframe.dataset.src && (!iframe.src || iframe.src === 'about:blank')) {
                    consoleLog('[LazyLoad] Iframe is intersecting, loading src:', iframe.dataset.src);
                    iframe.src = iframe.dataset.src;
                }
                observerInstance.unobserve(wrapper);
            } else {
                // Element is no longer visible
                if (wrapper.classList.contains('otk-tweet-embed-wrapper')) {
                    return; // Do not unload tweet embeds
                }

                if (iframe && iframe.src && iframe.src !== 'about:blank') {
                    consoleLog('[LazyLoad] Iframe is no longer intersecting, removing iframe for:', iframe.src);

                    // For YouTube, try to pause the video before removing
                    if (iframe.contentWindow && iframe.src.includes("youtube.com/embed")) {
                        try {
                            iframe.contentWindow.postMessage('{"event":"command","func":"pauseVideo","args":""}', 'https://www.youtube.com');
                        } catch (e) {
                            consoleWarn('[LazyLoad] Error attempting to postMessage pause to YouTube:', e);
                        }
                    } else if (iframe.contentWindow && iframe.src.includes("twitch.tv")) {
                        try {
                            iframe.contentWindow.postMessage({"event": "video.pause"}, "*");
                        } catch (e) {
                            consoleWarn('[LazyLoad] Error attempting to postMessage pause to Twitch:', e);
                        }
                    }

                    // Store the embed URL on the wrapper if it's not already there
                    if (!wrapper.dataset.embedUrl) {
                        wrapper.dataset.embedUrl = iframe.dataset.src;
                    }

                    // Remove the iframe and add a placeholder
                    iframe.remove();
                    const placeholder = document.createElement('div');
                    placeholder.textContent = 'Embed hidden. Scroll to load.';
                    placeholder.style.cssText = `
                        display: flex;
                        align-items: center;
                        justify-content: center;
                        width: 100%;
                        height: 100%;
                        background-color: #181818;
                        color: white;
                        font-size: 14px;
                    `;
                    wrapper.appendChild(placeholder);
                    observerInstance.observe(wrapper);
                }
            }
        });
    }

    let statAnimationFrameId = null;
let tabHidden = false;
let statAnimationTimers = [];

document.addEventListener("visibilitychange", () => {
  tabHidden = document.hidden;
});

    // Constants for storage keys
    const THREADS_KEY = 'otkActiveThreads';
    const MESSAGES_KEY = 'otkMessagesByThreadId';
    const COLORS_KEY = 'otkThreadColors';
    const DROPPED_THREADS_KEY = 'otkDroppedThreadIds';
    const BACKGROUND_UPDATES_DISABLED_KEY = 'otkBackgroundUpdatesDisabled';
    const DEBUG_MODE_KEY = 'otkDebugModeEnabled'; // For localStorage
    const LOCAL_IMAGE_COUNT_KEY = 'otkLocalImageCount';
    const LOCAL_VIDEO_COUNT_KEY = 'otkLocalVideoCount';
    const LAST_SEEN_MESSAGES_KEY = 'otkLastSeenMessagesCount';
    const LAST_SEEN_IMAGES_KEY = 'otkLastSeenImagesCount';
    const LAST_SEEN_VIDEOS_KEY = 'otkLastSeenVideosCount';
    const VIEWER_OPEN_KEY = 'otkViewerOpen'; // For viewer open/closed state
    const ANCHORED_MESSAGE_ID_KEY = 'otkAnchoredMessageId'; // For storing anchored message ID
    const ANCHORED_MESSAGE_CLASS = 'otk-anchored-message'; // CSS class for highlighting anchored message
    const MAX_QUOTE_DEPTH = 2; // Maximum depth for rendering nested quotes
    const SEEN_EMBED_URL_IDS_KEY = 'otkSeenEmbedUrlIds'; // For tracking unique text embeds for stats
    const OTK_TRACKED_KEYWORDS_KEY = 'otkTrackedKeywords'; // For user-defined keywords
    const OTK_BG_UPDATE_FREQ_SECONDS_KEY = 'otkBgUpdateFrequencySeconds'; // For background update frequency
    const TWEET_EMBED_MODE_KEY = 'otkTweetEmbedMode'; // For tweet embed theme
    const TWEET_CACHE_KEY = 'otkTweetCache'; // For caching tweet HTML
    const MAIN_THEME_KEY = 'otkMainTheme';
    const BLURRED_IMAGES_KEY = 'otkBlurredImages';
    const IMAGE_BLUR_AMOUNT_KEY = 'otkImageBlurAmount';
    const BLOCKED_THREADS_KEY = 'otkBlockedThreads';
    const FILTER_RULES_V2_KEY = 'otkFilterRulesV2';

    // --- Global variables ---
    let originalTitle = document.title;
    let otkViewer = null;
    let cityData = [];
    let tweetCache = {};
    try {
        tweetCache = JSON.parse(localStorage.getItem(TWEET_CACHE_KEY)) || {};
    } catch (e) {
        consoleError("Error parsing tweet cache from localStorage:", e);
    }
    let viewerActiveImageCount = null; // For viewer-specific unique image count
    let viewerActiveVideoCount = null; // For viewer-specific unique video count
    let backgroundRefreshIntervalId = null;
    let isManualRefreshInProgress = false;
    let isSuspended = false;
    const BACKGROUND_REFRESH_INTERVAL = 30000; // 30 seconds
    let lastViewerScrollTop = 0; // To store scroll position
    let renderedMessageIdsInViewer = new Set(); // To track IDs in viewer for incremental updates
    let uniqueImageViewerHashes = new Set(); // Global set for viewer's unique image hashes
    let threadFetchMetadata = {}; // For ETags / Last-Modified dates { threadId: { etag: "...", lastModified: "..." } }
    // let uniqueVideoViewerHashes = new Set(); // Removed as obsolete
    let viewerTopLevelAttachedVideoHashes = new Set(); // Viewer session: Hashes of ATTACHED videos in top-level messages
    let viewerTopLevelEmbedIds = new Set(); // Viewer session: Canonical IDs of EMBEDDED videos in top-level messages
    let renderedFullSizeImageHashes = new Set(); // Tracks image hashes already rendered full-size in current viewer session
    let mediaIntersectionObserver = null; // For lazy loading embeds
    let createdBlobUrls = new Set();
    let blurredImages = new Set();
    let blockedThreads = new Set();
    let cachedNewMessages = [];

    // IndexedDB instance
    let otkMediaDB = null;

    // Debug mode (load from localStorage, default to true)
    let DEBUG_MODE = localStorage.getItem(DEBUG_MODE_KEY) === null ? true : localStorage.getItem(DEBUG_MODE_KEY) === 'true';

    const consoleLog = (...args) => {
        if (DEBUG_MODE) {
            console.log('[OTK Tracker]', ...args);
        }
    };
    const consoleWarn = (...args) => {
        if (DEBUG_MODE) {
            console.warn('[OTK Tracker]', ...args);
        }
    };
    const consoleError = (...args) => {
        // Errors should probably always be logged, or at least have a separate toggle
        console.error('[OTK Tracker]', ...args);
    };


    // --- Loading Screen Elements Setup ---
    function setupLoadingScreen() {
        try {
            if (document.getElementById('otk-loading-overlay')) {
                consoleLog("Loading screen elements already exist.");
                return;
            }

            const overlay = document.createElement('div');
        overlay.id = 'otk-loading-overlay';
        overlay.style.cssText = `
            position: fixed;
            top: 86px; /* Height of otkGuiWrapper (85px) + border (1px) */
            left: 0;
            width: 100%;
            height: calc(100vh - 86px); /* Full viewport height minus GUI height */
            background-color: rgba(var(--otk-loading-overlay-bg-rgb, 0,0,0), var(--otk-loading-overlay-opacity, 0.8)); /* Use CSS variables */
            z-index: 100000; /* Ensure it's on top of everything, including viewer */
            display: none; /* Hidden by default */
            flex-direction: column;
            align-items: center;
            justify-content: center;
            font-family: Verdana, sans-serif;
            color: var(--otk-loading-text-color, white); /* Use CSS variable */
        `;

        const detailsElement = document.createElement('div');
        detailsElement.id = 'otk-loading-details';
        // Inherits color from parent overlay, specific text styling:
        detailsElement.style.cssText = `
            margin-bottom: 20px;
            font-size: 16px;
            white-space: pre-line; /* Allow \n to create line breaks */
            text-align: center; /* Ensure multi-line text is also centered */
        `;
        overlay.appendChild(detailsElement);

        const progressBarContainer = document.createElement('div');
        progressBarContainer.id = 'otk-progress-bar-container';
        progressBarContainer.style.cssText = `
            width: 60%;
            max-width: 400px;
            background-color: var(--otk-loading-progress-bar-bg-color, #333); /* Use CSS variable */
            border: 1px solid #555; /* Border color could also be a variable if needed */
            border-radius: 5px;
            padding: 2px;
        `;
        overlay.appendChild(progressBarContainer);

        const progressBar = document.createElement('div');
        progressBar.id = 'otk-progress-bar';
        progressBar.style.cssText = `
            width: 0%;
            height: 25px;
            background-color: var(--otk-loading-progress-bar-fill-color, #4CAF50); /* Use CSS variable */
            border-radius: 3px;
            text-align: center;
            line-height: 25px;
            color: var(--otk-loading-progress-bar-text-color, white); /* Use CSS variable */
            font-weight: bold;
            transition: width 0.3s ease;
        `;
        progressBarContainer.appendChild(progressBar);

        document.body.appendChild(overlay);
        consoleLog("Loading screen elements created and appended to body.");

        // Self-check diagnostics
        consoleLog('Attempting to verify loading screen elements immediately after creation:');
        consoleLog('  Overlay found by ID:', document.getElementById('otk-loading-overlay') !== null);
        consoleLog('  Details found by ID:', document.getElementById('otk-loading-details') !== null);
        consoleLog('  Progress bar container found by ID:', document.getElementById('otk-progress-bar-container') !== null);
        consoleLog('  Progress bar fill found by ID:', document.getElementById('otk-progress-bar') !== null);
        } catch (e) {
            consoleError('CRITICAL ERROR within setupLoadingScreen itself:', e);
        }
    }

    function showLoadingScreen(initialDetailsText = "Loading...") {
        const overlay = document.getElementById('otk-loading-overlay');
        const detailsElement = document.getElementById('otk-loading-details');
        const progressBarElement = document.getElementById('otk-progress-bar');

        if (!overlay || !detailsElement || !progressBarElement) {
            consoleError("Loading screen elements not found. Cannot show loading screen.");
            return;
        }

        detailsElement.textContent = initialDetailsText;
        progressBarElement.style.width = '0%';
        progressBarElement.textContent = '0%';
        overlay.style.display = 'flex'; // Use flex as per setupLoadingScreen styles
        consoleLog(`Loading screen shown. Details: ${initialDetailsText}`);
    }

    function hideLoadingScreen() {
        const overlay = document.getElementById('otk-loading-overlay');
        if (overlay) {
            overlay.style.display = 'none';
            consoleLog("Loading screen hidden.");

            // As a final failsafe for the stuck button issue, find the refresh button and ensure its state is visually correct.
            const btnRefresh = document.getElementById('otk-refresh-data-btn');
            if (btnRefresh && !btnRefresh.disabled) {
                btnRefresh.classList.remove('otk-button--active');
                // Re-apply the base background color directly to override any lingering :active styles.
                btnRefresh.style.backgroundColor = getComputedStyle(document.documentElement).getPropertyValue('--otk-button-bg-color').trim();
            }
        } else {
            consoleWarn("Loading screen overlay not found when trying to hide.");
        }
    }

    function showSuspendedScreen() {
        const overlay = document.createElement('div');
        overlay.id = 'otk-suspended-overlay';
        overlay.style.cssText = `
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background-color: rgba(0, 0, 0, 0.9);
            z-index: 100001;
            display: flex;
            align-items: center;
            justify-content: center;
            font-family: Verdana, sans-serif;
            color: white;
            font-size: 24px;
        `;
        overlay.textContent = 'Thread Tracker is suspended due to inactivity.';
        document.body.appendChild(overlay);
        document.title = "[Suspended] " + originalTitle;
    }

    function hideSuspendedScreen() {
        const overlay = document.getElementById('otk-suspended-overlay');
        if (overlay) {
            overlay.remove();
        }
        document.title = originalTitle;
    }

    function updateLoadingProgress(percentage, detailsText) {
        const detailsElement = document.getElementById('otk-loading-details');
        const progressBarElement = document.getElementById('otk-progress-bar');

        if (!progressBarElement || !detailsElement) {
            consoleError("Progress bar or details element not found. Cannot update loading progress.");
            return;
        }

        percentage = Math.max(0, Math.min(100, parseFloat(percentage))); // Clamp percentage & ensure number

        progressBarElement.style.width = percentage + '%';
        progressBarElement.textContent = Math.round(percentage) + '%';

        if (detailsText !== undefined && detailsText !== null) { // Allow empty string to clear details
            detailsElement.textContent = detailsText;
        }
        consoleLog(`Loading progress: ${Math.round(percentage)}%, Details: ${detailsText === undefined ? '(no change)' : detailsText }`);
    }


    // --- IndexedDB Initialization ---


    // --- Media Embedding Helper Functions ---
function createYouTubeEmbedElement(videoId, timestampStr) { // Removed isInlineEmbed parameter
    let startSeconds = 0;
    if (timestampStr) {
        // Try to parse timestamp like 1h2m3s or 2m3s or 3s or just 123 (YouTube takes raw seconds for ?t=)
        // More robust parsing might be needed if youtube itself uses 1m30s format in its ?t= parameter.
        // For now, assume ?t= is always seconds from the regex, or simple h/m/s format.
        // Regex for youtubeMatch already captures 't' as a string of digits or h/m/s.
        // Let's refine the parsing for h/m/s format.
        if (timestampStr.match(/^\d+$/)) { // Pure seconds e.g. t=123
             startSeconds = parseInt(timestampStr, 10) || 0;
        } else { // Attempt to parse 1h2m3s format
            const timeParts = timestampStr.match(/(?:(\d+)h)?(?:(\d+)m)?(?:(\d+)s?)?/);
            if (timeParts) {
                const hours = parseInt(timeParts[1], 10) || 0;
                const minutes = parseInt(timeParts[2], 10) || 0;
                const seconds = parseInt(timeParts[3], 10) || 0; // Also handles case like "123" if 's' is optional and no h/m
                if (hours > 0 || minutes > 0 || seconds > 0) { // ensure some part was parsed
                     startSeconds = (hours * 3600) + (minutes * 60) + seconds;
                } else if (timeParts[0] === timestampStr && !isNaN(parseInt(timestampStr,10)) ) { // fallback for plain numbers if regex above was too greedy with optional s
                    startSeconds = parseInt(timestampStr, 10) || 0;
                }
            }
        }
    }

    const embedUrl = `https://www.youtube.com/embed/${videoId}` + (startSeconds > 0 ? `?start=${startSeconds}&autoplay=0` : '?autoplay=0'); // Added autoplay=0

    // Create a wrapper for responsive iframe
    const wrapper = document.createElement('div');
    wrapper.className = 'otk-youtube-embed-wrapper'; // Base class
    // Add 'otk-embed-inline' if specific styling beyond size is still desired from CSS,
    // or remove if all styling is now direct. For now, let's assume it might still be useful for other tweaks.
    wrapper.classList.add('otk-embed-inline');

    wrapper.style.position = 'relative'; // Needed for the absolutely positioned iframe
    wrapper.style.overflow = 'hidden';   // Good practice for wrappers
    wrapper.style.margin = '10px 0';     // Consistent vertical margin
    wrapper.style.backgroundColor = '#000'; // Black background while loading

    // Universal fixed size for all YouTube embeds
    wrapper.style.width = '480px';
    wrapper.style.height = '270px'; // 16:9 aspect ratio for 480px width
    // No paddingBottom or conditional sizing logic needed anymore

    const iframe = document.createElement('iframe');
    iframe.style.position = 'absolute';
    iframe.style.top = '0';
    iframe.style.left = '0';
    iframe.style.width = '100%';
    iframe.style.height = '100%';
    iframe.setAttribute('frameborder', '0');
    iframe.setAttribute('allowfullscreen', 'true');
    iframe.setAttribute('allow', 'accelerometer; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share');

    const lazyLoadEnabled = (localStorage.getItem('otkLazyLoadYouTube') || 'true') === 'true';

    if (lazyLoadEnabled) {
        iframe.dataset.src = embedUrl;
        if (mediaIntersectionObserver) {
            mediaIntersectionObserver.observe(wrapper);
        } else {
            consoleWarn("[LazyLoad] mediaIntersectionObserver not ready. Iframe will load immediately:", iframe.dataset.src);
            iframe.src = iframe.dataset.src;
        }
    } else {
        iframe.src = embedUrl;
    }

    wrapper.appendChild(iframe);
    return wrapper;
}

// Helper function for processing text segments (either append as text or handle as quote)
function appendTextOrQuoteSegment(textElement, segment, quoteRegex, currentDepth, MAX_QUOTE_DEPTH, messagesByThreadId, uniqueImageViewerHashes, boardForLink, mediaLoadPromises, parentMessageId) {
    // Note: mediaLoadPromises is passed down in case quote recursion generates media elements that need tracking.
    // However, createMessageElementDOM for quotes currently passes an empty array for it. This could be enhanced.
    const quoteMatch = segment.match(quoteRegex);

    if (quoteMatch && segment.startsWith(quoteMatch[0])) { // Process as quote only if segment starts with it
        // Handle quote (potentially recursive)
        if (currentDepth >= MAX_QUOTE_DEPTH) {
            // At max depth, display quote link as text or a placeholder, but don't recurse
            // To match original behavior of skipping pure ">>123" lines at max depth:
            if (segment === quoteMatch[0]) return; // Skip pure quote link if it's the entire segment

            // If "text >>123" or ">>123 text" at max depth, treat as text
            textElement.appendChild(document.createTextNode(segment));
            return;
        }

        // Not at max depth, so process the quote
        const quotedMessageId = quoteMatch[1];
        let quotedMessageObject = null;
        for (const threadIdKey in messagesByThreadId) {
            if (messagesByThreadId.hasOwnProperty(threadIdKey)) {
                const foundMsg = messagesByThreadId[threadIdKey].find(m => m.id === Number(quotedMessageId));
                if (foundMsg) {
                    quotedMessageObject = foundMsg;
                    break;
                }
            }
        }

        if (quotedMessageObject) {
            const quotedElement = createMessageElementDOM(
                quotedMessageObject,
                                mediaLoadPromises, // Pass down the array for mediaLoadPromises for quotes
                uniqueImageViewerHashes,
                // uniqueVideoViewerHashes, // Removed
                quotedMessageObject.board || boardForLink,
                false, // isTopLevelMessage = false for quotes
                currentDepth + 1,
                null, // threadColor is not used for quoted message accents
                parentMessageId // Pass the PARENT message's ID for the quote
            );
            if (quotedElement) {
                if (currentDepth >= MAX_QUOTE_DEPTH - 1 && !quotedMessageObject.text) {
                    return;
                }
                textElement.appendChild(quotedElement);
            }
        } else {
            const notFoundSpan = document.createElement('span');
            notFoundSpan.textContent = `>>${quotedMessageId} (Not Found)`;
            notFoundSpan.style.color = '#88ccee';
            notFoundSpan.style.textDecoration = 'underline';
            textElement.appendChild(notFoundSpan);
        }

        const restOfSegment = segment.substring(quoteMatch[0].length);
        if (restOfSegment.length > 0) {
            // Recursively process the rest of the segment for more quotes or text
            // This is important if a line is like ">>123 >>456 text"
            appendTextOrQuoteSegment(textElement, restOfSegment, quoteRegex, currentDepth, MAX_QUOTE_DEPTH, messagesByThreadId, uniqueImageViewerHashes, boardForLink, mediaLoadPromises, parentMessageId);
        }
    } else {
        // Not a quote at the start of the segment (or not a quote at all), just plain text for this segment
        if (segment.length > 0) { // Ensure non-empty segment before creating text node
            textElement.appendChild(document.createTextNode(segment));
        }
    }
}

function createTwitchEmbedElement(type, id, timestampStr) {
    let embedUrl;
    const parentDomain = 'boards.4chan.org'; // Or dynamically get current hostname if needed for wider use

    if (type === 'clip_direct' || type === 'clip_channel') {
        embedUrl = `https://clips.twitch.tv/embed?clip=${id}&parent=${parentDomain}&autoplay=false`;
    } else if (type === 'vod') {
        let timeParam = '';
        if (timestampStr) {
            // Twitch expects format like 01h30m20s
            // The regex twitchTimestampRegex captures ((?:\d+h)?(?:\d+m)?(?:\d+s)?)
            // We need to ensure it's formatted correctly if only parts are present e.g. "30m10s" or "1h5s"
            // The regex already produces a string like "1h2m3s" or "45m" or "30s".
            // If it's just seconds, e.g. "120s", that's also valid.
            // If it's "120", it needs 's' appended. The regex ensures 's' if only seconds, or h/m present.
            // The regex `((?:\d+h)?(?:\d+m)?(?:\d+s)?)` might result in empty string if no t= is found.
            // And if t= is empty like `t=`, timestampStr would be empty.
            if (timestampStr.length > 0) { // Ensure timestampStr is not empty
                 timeParam = `&time=${timestampStr}`;
            }
        }
        embedUrl = `https://player.twitch.tv/?video=${id}&parent=${parentDomain}&autoplay=false${timeParam}`;
    } else {
        consoleError(`[EmbedTwitch] Unknown Twitch embed type: ${type}`);
        return document.createTextNode(`[Invalid Twitch Embed Type: ${type}]`);
    }

    const wrapper = document.createElement('div');
    // Apply common classes for potential shared styling, and specific for twitch
    wrapper.className = 'otk-twitch-embed-wrapper otk-embed-inline'; // All embeds are now 'inline' styled (fixed small size)

    wrapper.style.position = 'relative';
    wrapper.style.overflow = 'hidden';
    wrapper.style.margin = '10px 0'; // Consistent vertical margin
    wrapper.style.backgroundColor = '#181818'; // Twitchy background color

    // Universal fixed size for all embeds
    wrapper.style.width = '480px';
    wrapper.style.height = '270px'; // 16:9 aspect ratio for 480px width
    wrapper.dataset.embedUrl = embedUrl;

    const placeholder = document.createElement('div');
    placeholder.textContent = 'Twitch embed hidden. Scroll to load.';
    placeholder.style.cssText = `
        display: flex;
        align-items: center;
        justify-content: center;
        width: 100%;
        height: 100%;
        background-color: #181818;
        color: white;
        font-size: 14px;
    `;
    wrapper.appendChild(placeholder);

    if (mediaIntersectionObserver) {
        mediaIntersectionObserver.observe(wrapper);
    } else {
        consoleWarn("[LazyLoad] mediaIntersectionObserver not ready. Twitch embed will not lazy load.");
    }

    return wrapper;
}

function createKickEmbedElement(clipId) {
    const embedUrl = `https://kick.com/embed/clip/${clipId}`;

    const wrapper = document.createElement('div');
    wrapper.className = 'otk-kick-embed-wrapper otk-embed-inline';

    wrapper.style.position = 'relative';
    wrapper.style.overflow = 'hidden';
    wrapper.style.margin = '10px 0';
    wrapper.style.backgroundColor = '#111';

    wrapper.style.width = '480px';
    wrapper.style.height = '270px';

    const iframe = document.createElement('iframe');
    iframe.style.position = 'absolute';
    iframe.style.top = '0';
    iframe.style.left = '0';
    iframe.style.width = '100%';
    iframe.style.height = '100%';
    iframe.setAttribute('frameborder', '0');
    iframe.setAttribute('allowfullscreen', 'true');
    iframe.setAttribute('scrolling', 'no');

    const lazyLoadEnabled = (localStorage.getItem('otkLazyLoadKick') || 'true') === 'true';

    if (lazyLoadEnabled) {
        iframe.dataset.src = embedUrl;
        if (mediaIntersectionObserver) {
            mediaIntersectionObserver.observe(wrapper);
        } else {
            consoleWarn("[LazyLoad] mediaIntersectionObserver not ready. Iframe will load immediately:", iframe.dataset.src);
            iframe.src = iframe.dataset.src;
        }
    } else {
        iframe.src = embedUrl;
    }

    wrapper.appendChild(iframe);

    return wrapper;
}

function createTikTokEmbedElement(videoId) {
    const embedUrl = `https://www.tiktok.com/player/v1/${videoId}?autoplay=0`;

    const wrapper = document.createElement('div');
    wrapper.className = 'otk-tiktok-embed-wrapper otk-embed-inline';

    wrapper.style.position = 'relative';
    wrapper.style.overflow = 'hidden';
    wrapper.style.margin = '10px 0';
    wrapper.style.backgroundColor = '#000';

    wrapper.style.width = '325px';
    wrapper.style.height = '750px';

    const iframe = document.createElement('iframe');
    iframe.style.position = 'absolute';
    iframe.style.top = '0';
    iframe.style.left = '0';
    iframe.style.width = '100%';
    iframe.style.height = '100%';
    iframe.setAttribute('frameborder', '0');
    iframe.setAttribute('allowfullscreen', 'true');
    iframe.setAttribute('scrolling', 'no');

    const lazyLoadEnabled = (localStorage.getItem('otkLazyLoadTikTok') || 'true') === 'true';

    if (lazyLoadEnabled) {
        iframe.dataset.src = embedUrl;
        if (mediaIntersectionObserver) {
            mediaIntersectionObserver.observe(wrapper);
        } else {
            consoleWarn("[LazyLoad] mediaIntersectionObserver not ready. Iframe will load immediately:", iframe.dataset.src);
            iframe.src = iframe.dataset.src;
        }
    } else {
        iframe.src = embedUrl;
    }

    wrapper.appendChild(iframe);

    return wrapper;
}

function createStreamableEmbedElement(videoId) {
    // Streamable embed URL format is typically https://streamable.com/e/VIDEO_ID
    // Attempting to add loop=0 to disable looping.
    const embedUrl = `https://streamable.com/e/${videoId}?loop=0`;

    const wrapper = document.createElement('div');
    wrapper.className = 'otk-streamable-embed-wrapper otk-embed-inline'; // Common class for fixed-size embeds

    wrapper.style.position = 'relative';
    wrapper.style.overflow = 'hidden';
    wrapper.style.margin = '10px 0';     // Consistent vertical margin
    wrapper.style.backgroundColor = '#111'; // Dark background for Streamable

    // Universal fixed size for all embeds
    wrapper.style.width = '480px';
    wrapper.style.height = '270px'; // Assuming 16:9 for consistency, adjust if Streamable common aspect is different

    const iframe = document.createElement('iframe');
    iframe.style.position = 'absolute';
    iframe.style.top = '0';
    iframe.style.left = '0';
    iframe.style.width = '100%';
    iframe.style.height = '100%';
    iframe.setAttribute('frameborder', '0');
    iframe.setAttribute('allowfullscreen', 'true');
    iframe.setAttribute('scrolling', 'no');

    const lazyLoadEnabled = (localStorage.getItem('otkLazyLoadStreamable') || 'true') === 'true';

    if (lazyLoadEnabled) {
        iframe.dataset.src = embedUrl;
        if (mediaIntersectionObserver) {
            mediaIntersectionObserver.observe(wrapper);
        } else {
            consoleWarn("[LazyLoad] mediaIntersectionObserver not ready. Iframe will load immediately:", iframe.dataset.src);
            iframe.src = iframe.dataset.src;
        }
    } else {
        iframe.src = embedUrl;
    }

    wrapper.appendChild(iframe);

    return wrapper;
}


function createTweetEmbedElement(tweetId) {
    const tweetUrl = `https://twitter.com/any/status/${tweetId}`;
    const link = document.createElement('a');
    link.href = tweetUrl;
    link.textContent = tweetUrl;
    link.target = '_blank';
    return link;
}



    // --- Data Handling & Utility Functions ---
    function decodeAllHtmlEntities(html) {
        if (typeof html !== 'string' || html.length === 0) return '';
        let decoded = html;
        // Loop twice to handle cases like &amp;#039; -> &#039; -> '
        for (let i = 0; i < 2; i++) {
            const txt = document.createElement('textarea');
            txt.innerHTML = decoded;
            if (txt.value === decoded) { // If no change, decoding is complete for this pass
                break;
            }
            decoded = txt.value;
        }
        return decoded;
    }

    function toTitleCase(str) {
        if (!str) return '';
        let title = str.toLowerCase().replace(/\b\w/g, s => s.toUpperCase());
        // Special case for 'OTK'
        title = title.replace(/\botk\b/gi, 'OTK');
        return title;
    }

    function getAllMessagesSorted() {
        let allMessages = [];
        const allThreadIds = Object.keys(messagesByThreadId);
        for (const threadId of allThreadIds) {
            if (messagesByThreadId.hasOwnProperty(threadId) && Array.isArray(messagesByThreadId[threadId])) {
                allMessages = allMessages.concat(messagesByThreadId[threadId]);
            }
        }
        allMessages.sort((a, b) => a.time - b.time); // Sort by timestamp ascending
        consoleLog(`Collected and sorted ${allMessages.length} messages from all locally stored threads.`);
        return allMessages;
    }

    async function recalculateAndStoreMediaStats() {
        if (!otkMediaDB) {
            consoleWarn("Cannot recalculate media stats: IndexedDB not available.");
            // Ensure localStorage is at least zeroed out if DB isn't there
            localStorage.setItem(LOCAL_IMAGE_COUNT_KEY, '0');
            localStorage.setItem(LOCAL_VIDEO_COUNT_KEY, '0');
            return { imageCount: 0, videoCount: 0 };
        }

        consoleLog("Recalculating local media statistics from IndexedDB...");
        return new Promise((resolve, reject) => {
            let imageCount = 0;
            let videoCount = 0;

            const transaction = otkMediaDB.transaction(['mediaStore'], 'readonly');
            const store = transaction.objectStore('mediaStore');
            const request = store.openCursor();

            request.onsuccess = (event) => {
                const cursor = event.target.result;
                if (cursor) {
                    const item = cursor.value;
                    if (item && item.ext) {
                        const ext = item.ext.toLowerCase();
                        if (['.jpg', '.jpeg', '.png', '.gif'].includes(ext)) {
                            imageCount++;
                        } else if (['.webm', '.mp4'].includes(ext)) {
                            videoCount++;
                        }
                    }
                    cursor.continue();
                } else {
                    // Cursor finished
                    localStorage.setItem(LOCAL_IMAGE_COUNT_KEY, imageCount.toString());
                    localStorage.setItem(LOCAL_VIDEO_COUNT_KEY, videoCount.toString());
                    consoleLog(`Recalculated stats: ${imageCount} images, ${videoCount} videos. Stored to localStorage.`);
                    resolve({ imageCount, videoCount });
                }
            };

            request.onerror = (event) => {
                consoleError("Error recalculating media stats from IndexedDB:", event.target.error);
                // Don't clear localStorage here, might have valid old counts. Or do? For safety, let's clear.
                localStorage.setItem(LOCAL_IMAGE_COUNT_KEY, '0');
                localStorage.setItem(LOCAL_VIDEO_COUNT_KEY, '0');
                reject(event.target.error);
            };
        });
    }

    async function initDB() {
        return new Promise((resolve, reject) => {
            consoleLog('Initializing IndexedDB...');
            const request = indexedDB.open('otkMediaDB', 3); // DB name and version - Incremented to 3

            request.onupgradeneeded = (event) => {
                const db = event.target.result;
                consoleLog(`Upgrading IndexedDB from version ${event.oldVersion} to ${event.newVersion}.`);
                if (!db.objectStoreNames.contains('mediaStore')) {
                    const store = db.createObjectStore('mediaStore', { keyPath: 'filehash' });
                    store.createIndex('threadId', 'threadId', { unique: false });
                    consoleLog('MediaStore object store created with filehash as keyPath and threadId index.');
                }
                if (!db.objectStoreNames.contains('messagesStore')) {
                    const messagesStore = db.createObjectStore('messagesStore', { keyPath: 'threadId' });
                    consoleLog('MessagesStore object store created with threadId as keyPath.');
                }
            };

            request.onsuccess = (event) => {
                otkMediaDB = event.target.result;
                consoleLog('IndexedDB initialized successfully.');
                resolve(otkMediaDB);
            };

            request.onerror = (event) => {
                consoleError('IndexedDB initialization error:', event.target.error);
                otkMediaDB = null; // Ensure it's null on error
                reject(event.target.error);
            };
        });
    }

    // Color palette for thread indicators
    const COLORS = [
        '#e6194B', '#3cb44b', '#ffe119', '#4363d8', '#f58231',
        '#911eb4', '#46f0f0', '#f032e6', '#bcf60c',
        '#008080', '#e6beff', '#9A6324', '#800000',
        '#aaffc3', '#808000', '#ffd8b1', '#000075', '#808080'
    ];

    // --- GUI Setup ---
    // Create GUI structure
    let otkGuiWrapper = document.getElementById('otk-tracker-gui-wrapper');
    let otkGui = document.getElementById('otk-tracker-gui');

    if (!otkGuiWrapper) {
        otkGuiWrapper = document.createElement('div');
        otkGuiWrapper.id = 'otk-tracker-gui-wrapper';
        otkGuiWrapper.style.cssText = `
            position: fixed;
            top: 0;
            left: 0;
            width: 100vw;
            z-index: 9999;
            border-bottom: 4px solid var(--otk-gui-bottom-border-color);
            background: var(--otk-gui-bg-color);
            box-sizing: border-box;
            box-shadow: 0 2px 5px rgba(0,0,0,0.2);
        `;

        otkGui = document.createElement('div');
        otkGui.id = 'otk-tracker-gui';
        otkGui.style.cssText = `
            height: 85px;
            color: var(--otk-gui-text-color); /* This is now for general GUI text */
            font-family: Verdana, sans-serif;
            font-size: 14px;
            padding: 5px 25px;
            box-sizing: border-box;
            display: flex;
            align-items: stretch;
            user-select: none;
            position: relative;
            justify-content: space-between;
        `;
        otkGuiWrapper.appendChild(otkGui);
        document.body.style.paddingTop = '86px';
        document.body.insertBefore(otkGuiWrapper, document.body.firstChild);

        // Thread display container (left)
        const threadDisplayContainer = document.createElement('div');
        threadDisplayContainer.id = 'otk-thread-display-container';
        threadDisplayContainer.style.cssText = `
            display: flex;
            flex-direction: column;
            justify-content: flex-start;
            padding-top: 3px;
            padding-bottom: 5px;
            max-width: 450px;
            flex-grow: 0;
            flex-shrink: 0;
            justify-content: center;
        `;
        otkGui.appendChild(threadDisplayContainer);

        // Center info container
        const centerInfoContainer = document.createElement('div');
        centerInfoContainer.id = 'otk-center-info-container';
        centerInfoContainer.style.cssText = `
            position: absolute;
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            padding: 0 10px;
            pointer-events: none;
        `;

        // Wrapper for title and stats to keep them left-aligned but centered as a block
        const statsWrapper = document.createElement('div');
        statsWrapper.id = 'otk-stats-wrapper';
        statsWrapper.style.cssText = `
            margin-bottom: 4px;
            display: flex;
            flex-direction: column;
            align-items: flex-start; /* Left-align title and stats */
            width: fit-content; /* Only as wide as needed */
            max-width: 250px; /* Prevent excessive width */
            pointer-events: auto;
        `;

        const otkThreadTitleDisplay = document.createElement('div');
        otkThreadTitleDisplay.id = 'otk-thread-title-display';
        otkThreadTitleDisplay.textContent = 'Thread Tracker 2.7';
        otkThreadTitleDisplay.style.cssText = `
            font-weight: bold;
            font-size: 14px;
            display: inline;
            color: var(--otk-title-text-color);
        `;

        const cogIcon = document.createElement('span');
        cogIcon.id = 'otk-settings-cog';
        cogIcon.innerHTML = '⚙';
        cogIcon.style.cssText = `
            font-size: 16px;
            margin-left: 10px;
            cursor: pointer;
            display: inline-block;
            color: var(--otk-cog-icon-color);
        `;
        cogIcon.title = "Open Settings";

        const titleContainer = document.createElement('div');
        titleContainer.style.cssText = `
            display: flex;
            align-items: baseline;
            justify-content: flex-start; /* Left-align title and cog */
            margin-bottom: 4px;
        `;
        titleContainer.appendChild(otkThreadTitleDisplay);
        titleContainer.appendChild(cogIcon);


        const otkStatsDisplay = document.createElement('div');
        otkStatsDisplay.id = 'otk-stats-display';
        otkStatsDisplay.style.cssText = `
            font-size: 11px;
            display: flex;
            flex-direction: column;
            align-items: flex-start;
            width: fit-content;
            min-width: 200px; /* Reserve space for (+n) */
        `;

        const threadsTrackedStat = document.createElement('div');
        threadsTrackedStat.id = 'otk-threads-tracked-stat';
        threadsTrackedStat.style.cssText = `
            display: flex;
            align-items: center;
            color: var(--otk-stats-text-color);
            min-width: 200px; /* Prevent shifting from (+n) */
            white-space: nowrap;
        `;

        const totalMessagesStat = document.createElement('div');
        totalMessagesStat.id = 'otk-total-messages-stat';
        totalMessagesStat.style.cssText = `
            display: flex;
            align-items: center;
            color: var(--otk-stats-text-color);
            min-width: 200px;
            white-space: nowrap;
        `;

        const localImagesStat = document.createElement('div');
        localImagesStat.id = 'otk-local-images-stat';
        localImagesStat.style.cssText = `
            display: flex;
            align-items: center;
            color: var(--otk-stats-text-color);
            min-width: 200px;
            white-space: nowrap;
        `;

        const localVideosStat = document.createElement('div');
        localVideosStat.id = 'otk-local-videos-stat';
        localVideosStat.style.cssText = `
            display: flex;
            align-items: center;
            color: var(--otk-stats-text-color);
            min-width: 200px;
            white-space: nowrap;
        `;

        otkStatsDisplay.appendChild(threadsTrackedStat);
        otkStatsDisplay.appendChild(totalMessagesStat);
        otkStatsDisplay.appendChild(localImagesStat);
        otkStatsDisplay.appendChild(localVideosStat);

        statsWrapper.appendChild(titleContainer);
        statsWrapper.appendChild(otkStatsDisplay);
        centerInfoContainer.appendChild(statsWrapper);
        otkGui.appendChild(centerInfoContainer);

        // Button container (right)
        const buttonContainer = document.createElement('div');
        buttonContainer.id = 'otk-button-container';
        buttonContainer.style.cssText = `
            display: flex;
            flex-direction: column;     /* Stack children vertically */
            align-items: flex-end;      /* Align children (top/bottom rows) to the right */
            justify-content: center;    /* Center the buttons vertically */
            gap: 5px;                   /* Small gap between top and bottom rows if needed */
            height: 100%;               /* Occupy full height of parent for space-between */
        `;
        otkGui.appendChild(buttonContainer);
    } else { // If GUI wrapper exists, ensure consistency
        if (document.body.style.paddingTop !== '86px') {
            document.body.style.paddingTop = '86px';
        }

        if (!otkGui) { // Re-create otkGui if missing
            otkGui = document.createElement('div');
            otkGui.id = 'otk-tracker-gui';
            // Apply styles as in initial creation
            otkGui.style.cssText = `
                height: 85px;
                color: var(--otk-gui-text-color); /* This is now for general GUI text */
                font-family: Verdana, sans-serif;
                font-size: 14px;
                padding: 5px 25px;
                box-sizing: border-box;
                display: flex;
                align-items: stretch;
                user-select: none;
            `;
            otkGuiWrapper.appendChild(otkGui);
        }

        // Ensure sub-containers exist
        if (!document.getElementById('otk-thread-display-container')) {
            const threadDisplayContainer = document.createElement('div');
            threadDisplayContainer.id = 'otk-thread-display-container';
            // Apply styles
             threadDisplayContainer.style.cssText = `
                display: flex;
                flex-direction: column;
                justify-content: flex-start;
                padding-top: 3px;
                padding-bottom: 5px;
                max-width: 450px;
                flex-grow: 0;
                flex-shrink: 0;
                justify-content: center;
            `;
            const existingButtonContainer = otkGui.querySelector('#otk-button-container');
            if (existingButtonContainer) {
                otkGui.insertBefore(threadDisplayContainer, existingButtonContainer);
            } else {
                otkGui.appendChild(threadDisplayContainer);
            }
        }

        if (!document.getElementById('otk-center-info-container')) {
            const centerInfoContainer = document.createElement('div');
            centerInfoContainer.id = 'otk-center-info-container';
            // Apply styles
            centerInfoContainer.style.cssText = `
                flex-grow: 1; /* Ensures it takes available space */
                display: flex;
                flex-direction: column;
                align-items: center;
                justify-content: center; /* Center the new parent container vertically */
                color: white;
                text-align: center;
                padding: 0 10px;
            `;
            consoleLog('[GUI Setup - Reconstruction] centerInfoContainer.style.flexGrow explicitly set to 1.');

            const otkThreadTitleDisplay = document.createElement('div');
            otkThreadTitleDisplay.id = 'otk-thread-title-display';
            otkThreadTitleDisplay.textContent = 'Thread Tracker 2.7'; // Updated version
            otkThreadTitleDisplay.style.cssText = `
                font-weight: bold; font-size: 14px; display: inline;
                color: var(--otk-title-text-color); /* Apply specific color variable */
            `; // Removed margin-bottom, display inline

            const cogIcon = document.createElement('span');
            cogIcon.id = 'otk-settings-cog'; // Ensure ID is consistent if needed for re-binding
            cogIcon.innerHTML = '&#x2699;';
            cogIcon.style.cssText = `
                font-size: 16px; margin-left: 10px; cursor: pointer; display: inline-block; vertical-align: middle; color: var(--otk-cog-icon-color);
            `;
            cogIcon.title = "Open Settings";
            // Note: Event listener for cog a V2 feature, or needs to be re-attached if GUI is rebuilt this way.
            // For now, just ensuring structure. If setupOptionsWindow is called after this, it might re-bind.

            const titleAndStatsContainer = document.createElement('div');
            titleAndStatsContainer.style.cssText = `
                display: flex;
                flex-direction: column;
                align-items: center;
            `;

            const titleContainer = document.createElement('div');
            titleContainer.style.cssText = `
                display: flex; align-items: center; justify-content: center; margin-bottom: 4px;
            `;
            titleContainer.appendChild(otkThreadTitleDisplay);
            titleContainer.appendChild(cogIcon);

            const otkStatsDisplay = document.createElement('div');
            otkStatsDisplay.id = 'otk-stats-display';
            otkStatsDisplay.style.cssText = `
                font-size: 11px;
                display: flex;
                flex-direction: column;
                align-items: flex-start; /* Left-align the stats */
                width: fit-content; /* Make block only as wide as its content */
            `;

            const threadsTrackedStat = document.createElement('div');
            threadsTrackedStat.id = 'otk-threads-tracked-stat';
            threadsTrackedStat.style.display = 'flex';

            const totalMessagesStat = document.createElement('div');
            totalMessagesStat.id = 'otk-total-messages-stat';
            totalMessagesStat.style.display = 'flex';

            const localImagesStat = document.createElement('div');
            localImagesStat.id = 'otk-local-images-stat';
            localImagesStat.style.display = 'flex';

            const localVideosStat = document.createElement('div');
            localVideosStat.id = 'otk-local-videos-stat';
            localVideosStat.style.display = 'flex';

            otkStatsDisplay.appendChild(threadsTrackedStat);
            otkStatsDisplay.appendChild(totalMessagesStat);
            otkStatsDisplay.appendChild(localImagesStat);
            otkStatsDisplay.appendChild(localVideosStat);

            titleAndStatsContainer.appendChild(titleContainer);
            titleAndStatsContainer.appendChild(otkStatsDisplay);
            centerInfoContainer.appendChild(titleAndStatsContainer);


            const existingButtonContainer = otkGui.querySelector('#otk-button-container');
            if (existingButtonContainer) {
                otkGui.insertBefore(centerInfoContainer, existingButtonContainer);
            } else {
                otkGui.appendChild(centerInfoContainer);
            }
        }

        if (!document.getElementById('otk-button-container')) {
            const buttonContainer = document.createElement('div');
            buttonContainer.id = 'otk-button-container';
            // Apply styles
            buttonContainer.style.cssText = `
                display: flex;
                align-items: flex-end; /* Consistent with initial creation */
                gap: 10px;
            `;
            buttonContainer.style.marginLeft = 'auto'; // Ensure right alignment
            consoleLog('[GUI Setup - Reconstruction] buttonContainer.style.marginLeft explicitly set to "auto".');
            otkGui.appendChild(buttonContainer);
        }
        // Update title if it exists and shows old version
        const titleDisplay = document.getElementById('otk-thread-title-display');
        if (titleDisplay && titleDisplay.textContent !== 'Thread Tracker 2.7') {
            titleDisplay.textContent = 'Thread Tracker 2.7';
        }
    }


    // --- Data Loading and Initialization ---
    function saveMessagesToDB(threadId, messages) {
        if (!otkMediaDB) {
            consoleError("DB not available, cannot save messages.");
            return Promise.reject("DB not available");
        }
        consoleLog(`Saving ${messages.length} messages for thread ${threadId} to DB.`);
        return new Promise((resolve, reject) => {
            const transaction = otkMediaDB.transaction(['messagesStore'], 'readwrite');
            transaction.oncomplete = () => {
                consoleLog(`Transaction to save messages for thread ${threadId} completed.`);
                resolve();
            };
            transaction.onerror = (event) => {
                consoleError(`Error saving messages for thread ${threadId} to DB:`, event.target.error);
                reject(event.target.error);
            };
            const store = transaction.objectStore('messagesStore');
            store.put({ threadId: threadId, messages: messages });
        });
    }

    function loadMessagesFromDB() {
        if (!otkMediaDB) {
            consoleError("DB not available, cannot load messages.");
            return Promise.resolve({});
        }
        return new Promise((resolve, reject) => {
            const transaction = otkMediaDB.transaction(['messagesStore'], 'readonly');
            const store = transaction.objectStore('messagesStore');
            const request = store.getAll();
            request.onsuccess = () => {
                const messagesById = {};
                if (Array.isArray(request.result)) {
                    for (const item of request.result) {
                        messagesById[item.threadId] = item.messages;
                    }
                }
                consoleLog("Messages loaded from DB: ", messagesById);
                resolve(messagesById);
            };
            request.onerror = (event) => {
                consoleError("Error loading messages from DB:", event.target.error);
                reject(event.target.error);
            };
        });
    }

    let activeThreads = [];
    try {
        activeThreads = JSON.parse(localStorage.getItem(THREADS_KEY)) || [];
    } catch (e) {
        consoleError("Error parsing active threads from localStorage:", e);
    }
    let messagesByThreadId = {}; // Will be populated from DB
    let threadColors = {};
    try {
        threadColors = JSON.parse(localStorage.getItem(COLORS_KEY)) || {};
    } catch (e) {
        consoleError("Error parsing thread colors from localStorage:", e);
    }
    let droppedThreadIds = [];
    try {
        droppedThreadIds = JSON.parse(localStorage.getItem(DROPPED_THREADS_KEY)) || [];
    } catch (e) {
        consoleError("Error parsing dropped thread IDs from localStorage:", e);
    }

    // Normalize thread IDs and exclude known dropped threads
    droppedThreadIds = droppedThreadIds.map(id => Number(id)).filter(id => !isNaN(id));
    activeThreads = activeThreads
        .map(id => Number(id))
        .filter(id => !isNaN(id) && !droppedThreadIds.includes(id));

    // The following loop is commented out to prevent messages from being deleted on startup.
    // for (const threadId in messagesByThreadId) {
    //     if (!activeThreads.includes(Number(threadId))) {
    //         consoleLog(`Removing thread ${threadId} from messagesByThreadId during initialization (not in activeThreads or in droppedThreadIds).`);
    //         delete messagesByThreadId[threadId];
    //         delete threadColors[threadId];
    //     }
    // }
    // Clean up droppedThreadIds after processing
    localStorage.removeItem(DROPPED_THREADS_KEY); // This seems to be a one-time cleanup
    localStorage.setItem(THREADS_KEY, JSON.stringify(activeThreads));
    localStorage.setItem(COLORS_KEY, JSON.stringify(threadColors));
    consoleLog('Initialized activeThreads from localStorage:', activeThreads);


    // (+n) Stat Update Logic
function resetPlusN() {
  const el = document.querySelector('.z-stats .z-new');
  if (el) {
    el.textContent = '';
    el.style.opacity = '0';
    el.classList.remove('active');
  }
  if (statAnimationFrameId) {
    cancelAnimationFrame(statAnimationFrameId);
    statAnimationFrameId = null;
  }
}

function animateStatIncrease(statEl, plusNEl, from, to) {
  const duration = 600;
  const start = performance.now();

  plusNEl.textContent = `+${to - from}`;
  plusNEl.style.opacity = '1';
  plusNEl.classList.add('active');

  function animate(time) {
    const progress = Math.min(1, (time - start) / duration);
    const currentVal = Math.floor(from + (to - from) * progress);
    statEl.textContent = currentVal;

    if (progress < 1) {
      statAnimationFrameId = requestAnimationFrame(animate);
    } else {
      statEl.textContent = to;
      setTimeout(resetPlusN, 1200);
      statAnimationFrameId = null;
    }
  }

  statAnimationFrameId = requestAnimationFrame(animate);
}

// --- Utility functions ---
    function blobToDataURL(blob) {
        return new Promise((resolve, reject) => {
            const reader = new FileReader();
            reader.onloadend = () => resolve(reader.result);
            reader.onerror = reject;
            reader.readAsDataURL(blob);
        });
    }

    function padNumber(num, length) {
        return String(num).padStart(length, '0');
    }

    function updateCountdown() {
        const nextUpdateTimestamp = parseInt(localStorage.getItem('otkNextUpdateTimestamp') || '0', 10);
        const countdownTimer = document.getElementById('otk-countdown-timer');
        if (!countdownTimer) {
            return;
        }

        const now = Date.now();
        const timeLeft = Math.max(0, nextUpdateTimestamp - now);
        const hours = Math.floor(timeLeft / (1000 * 60 * 60));
        const minutes = Math.floor((timeLeft % (1000 * 60 * 60)) / (1000 * 60));
        const seconds = Math.floor((timeLeft % (1000 * 60)) / 1000);

        countdownTimer.textContent = `${padNumber(hours, 2)}:${padNumber(minutes, 2)}:${padNumber(seconds, 2)}`;
    }

    function hexToRgbParts(hex) {
        if (!hex) return '0,0,0'; // Default to black if invalid input
        let shorthandRegex = /^#?([a-f\d])([a-f\d])([a-f\d])$/i;
        hex = hex.replace(shorthandRegex, function(m, r, g, b) {
            return r + r + g + g + b + b;
        });

        let result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
        if (result) {
            const r = parseInt(result[1], 16);
            const g = parseInt(result[2], 16);
            const b = parseInt(result[3], 16);
            return `${r},${g},${b}`;
        }
        return '0,0,0'; // Fallback to black if full hex parsing fails
    }

    function decodeEntities(encodedString) {
        const txt = document.createElement('textarea');
        txt.innerHTML = encodedString;
        return txt.value;
    }

    function truncateTitleWithWordBoundary(title, maxLength) {
        if (title.length <= maxLength) return title;
        let truncated = title.substr(0, maxLength);
        let lastSpace = truncated.lastIndexOf(' ');
        if (lastSpace > 0 && lastSpace > maxLength - 20) { // Ensure lastSpace is meaningful
            return truncated.substr(0, lastSpace) + '...';
        }
        return title.substr(0, maxLength - 3) + '...'; // Fallback if no good space
    }

    // --- Color Similarity Functions ---
    const SIMILARITY_THRESHOLD = 20; // Lower is more similar. 1-5 is imperceptible, >10 is distinct.

    function hexToRgb(hex) {
        let shorthandRegex = /^#?([a-f\d])([a-f\d])([a-f\d])$/i;
        hex = hex.replace(shorthandRegex, (m, r, g, b) => r + r + g + g + b + b);
        let result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
        return result ? {
            r: parseInt(result[1], 16),
            g: parseInt(result[2], 16),
            b: parseInt(result[3], 16)
        } : null;
    }

    function rgbToLab(rgb) {
        let r = rgb.r / 255, g = rgb.g / 255, b = rgb.b / 255;
        r = (r > 0.04045) ? Math.pow((r + 0.055) / 1.055, 2.4) : r / 12.92;
        g = (g > 0.04045) ? Math.pow((g + 0.055) / 1.055, 2.4) : g / 12.92;
        b = (b > 0.04045) ? Math.pow((b + 0.055) / 1.055, 2.4) : b / 12.92;

        let x = (r * 0.4124 + g * 0.3576 + b * 0.1805) / 0.95047;
        let y = (r * 0.2126 + g * 0.7152 + b * 0.0722) / 1.00000;
        let z = (r * 0.0193 + g * 0.1192 + b * 0.9505) / 1.08883;

        x = (x > 0.008856) ? Math.pow(x, 1/3) : (7.787 * x) + 16/116;
        y = (y > 0.008856) ? Math.pow(y, 1/3) : (7.787 * y) + 16/116;
        z = (z > 0.008856) ? Math.pow(z, 1/3) : (7.787 * z) + 16/116;

        return { l: (116 * y) - 16, a: 500 * (x - y), b: 200 * (y - z) };
    }

    function deltaE(labA, labB){
        const deltaL = labA.l - labB.l;
        const deltaA = labA.a - labB.a;
        const deltaB = labA.b - labB.b;
        return Math.sqrt(Math.pow(deltaL, 2) + Math.pow(deltaA, 2) + Math.pow(deltaB, 2));
    }

    function getThreadColor(threadId) {
        if (threadColors[threadId]) {
            return threadColors[threadId];
        }

        const usedColorHexes = new Set(Object.values(threadColors));
        const availableColors = COLORS.filter(c => !usedColorHexes.has(c));

        if (availableColors.length === 0) {
            // All colors from the palette are used, assign a fallback.
            const fallbackColor = '#888';
            threadColors[threadId] = fallbackColor;
            localStorage.setItem(COLORS_KEY, JSON.stringify(threadColors));
            return fallbackColor;
        }

        if (usedColorHexes.size === 0) {
            // If no colors are in use, any color is fine. Pick a random one.
            const randomColor = availableColors[Math.floor(Math.random() * availableColors.length)];
            threadColors[threadId] = randomColor;
            localStorage.setItem(COLORS_KEY, JSON.stringify(threadColors));
            return randomColor;
        }

        const usedLabColors = Array.from(usedColorHexes).map(hex => rgbToLab(hexToRgb(hex)));

        // For each available color, find its minimum distance to any of the used colors.
        const colorDistances = availableColors.map(candidateHex => {
            const candidateLab = rgbToLab(hexToRgb(candidateHex));
            const minDistance = Math.min(
                ...usedLabColors.map(usedLab => deltaE(candidateLab, usedLab))
            );
            return { color: candidateHex, distance: minDistance };
        });

        // Sort the candidates by their minimum distance in descending order.
        colorDistances.sort((a, b) => b.distance - a.distance);

        // The best candidate is the one with the largest minimum distance.
        const colorToAssign = colorDistances[0].color;

        threadColors[threadId] = colorToAssign;
        localStorage.setItem(COLORS_KEY, JSON.stringify(threadColors));
        return colorToAssign;
    }

    function toggleImageBlur(filehash) {
        if (blurredImages.has(filehash)) {
            blurredImages.delete(filehash);
        } else {
            blurredImages.add(filehash);
        }

        localStorage.setItem(BLURRED_IMAGES_KEY, JSON.stringify(Array.from(blurredImages)));

        // Update all images on the page
        const allImagesOnPage = document.querySelectorAll(`img[data-filehash="${filehash}"]`);
        const blurAmount = (localStorage.getItem(IMAGE_BLUR_AMOUNT_KEY) || 60) / 5;
        const isBlurred = blurredImages.has(filehash);

        allImagesOnPage.forEach(img => {
            img.style.filter = isBlurred ? `blur(${blurAmount}px)` : 'none';
        });
        consoleLog(`Toggled blur for ${filehash}. Now blurred: ${isBlurred}`);
    }

    // --- Core Logic: Rendering, Fetching, Updating ---

    function findMessageById(messageId) {
        messageId = Number(messageId);
        for (const threadId in messagesByThreadId) {
            if (messagesByThreadId.hasOwnProperty(threadId)) {
                const foundMsg = messagesByThreadId[threadId].find(m => m.id === messageId);
                if (foundMsg) {
                    return foundMsg;
                }
            }
        }
        return null;
    }

function findMessageDepth(message, targetId, currentDepth = 0) {
    if (String(message.id) === String(targetId)) {
        return currentDepth;
    }
    if (currentDepth < MAX_QUOTE_DEPTH && message.text) {
        const quoteRegex = />>(\d+)/g;
        let match;
        const uniqueQuoteIds = new Set();
        while ((match = quoteRegex.exec(message.text)) !== null) {
            uniqueQuoteIds.add(match[1]);
        }
        for (const quotedMessageId of uniqueQuoteIds) {
            const quotedMessageObject = findMessageById(quotedMessageId);
            if (quotedMessageObject) {
                const foundDepth = findMessageDepth(quotedMessageObject, targetId, currentDepth + 1);
                if (foundDepth !== null) {
                    return foundDepth;
                }
            }
        }
    }
    return null;
}

function hasTruncatedQuotes(message, currentDepth = 0) {
    if (currentDepth === MAX_QUOTE_DEPTH) {
        return message.text && />>(\d+)/.test(message.text);
    }
    if (currentDepth < MAX_QUOTE_DEPTH) {
        if (!message.text) return false;
        const quoteRegex = />>(\d+)/g;
        let match;
        const uniqueQuoteIds = new Set();
        while ((match = quoteRegex.exec(message.text)) !== null) {
            uniqueQuoteIds.add(match[1]);
        }
        for (const quotedMessageId of uniqueQuoteIds) {
            const quotedMessageObject = findMessageById(quotedMessageId);
            if (quotedMessageObject && hasTruncatedQuotes(quotedMessageObject, currentDepth + 1)) {
                return true;
            }
        }
    }
    return false;
}

function findNextUnloadedQuoteLink(topLevelElement) {
    // 1. Find all message elements within the top-level container.
    const allMessageElements = Array.from(topLevelElement.querySelectorAll('div[data-message-id]'));
    const renderedMessageIds = new Set(allMessageElements.map(el => el.dataset.messageId));

    // 2. Iterate through all rendered messages to find quote links.
    for (const messageElement of allMessageElements) {
        const messageId = messageElement.dataset.messageId;
        const messageObject = findMessageById(messageId);

        if (messageObject && messageObject.text) {
            const quoteRegex = />>(\d+)/g;
            let match;
            while ((match = quoteRegex.exec(messageObject.text)) !== null) {
                const quotedId = match[1];

                // 3. Check if the found quote link points to a message that is NOT already rendered.
                if (!renderedMessageIds.has(quotedId)) {
                    // This is a "leaf" node. We've found the next link to load.
                    return {
                        id: quotedId,
                        parentId: messageId, // The parent for insertion is the element containing the link.
                    };
                    }
                }
            }
        }

    // 4. If we loop through everything and find no unloaded links, return null.
        return null;
    }

function isMessageFiltered(message, rules) {
    const messageText = (message.text || '').toLowerCase();
    const messageMd5 = message.attachment?.filehash_db_key || '';

    const matchingFilterOutRule = rules.find(rule => {
        if (!rule.enabled || rule.action !== 'filterOut') {
            return false;
        }

        const matchContent = rule.matchContent; // Keep case for JSON parsing
        if (!matchContent) return false;

        switch (rule.category) {
            case 'keyword':
                return messageText.includes(matchContent.toLowerCase());
            case 'attachedMedia':
                // Do not convert to lower case, as MD5 (base64) is case sensitive.
                return messageMd5 === matchContent.replace('md5:', '');
            case 'entireMessage':
                try {
                    const conditions = JSON.parse(matchContent);
                    const textMatch = conditions.text ? messageText.includes(conditions.text.toLowerCase()) : true;
                    // Do not convert to lower case for media hash
                    const mediaHashInRule = conditions.media ? conditions.media.replace('md5:', '') : null;
                    const mediaMatch = mediaHashInRule ? messageMd5 === mediaHashInRule : true;
                    return textMatch && mediaMatch;
                } catch (e) {
                    return messageText.includes(matchContent.toLowerCase());
                }
            case 'embeddedLink':
                const urlRegex = /(https?:\/\/[^\s]+)/g;
                let urls;
                while ((urls = urlRegex.exec(message.text || '')) !== null) { // Use original case text for this check
                    if (urls[0].toLowerCase().includes(matchContent.toLowerCase())) {
                        return true;
                    }
                }
                return false;
            default:
                return false;
        }
    });

    return !!matchingFilterOutRule;
}

function doesAnyRuleMatch(message, rules) {
    const messageText = (message.text || '').toLowerCase();
    const messageMd5 = message.attachment?.filehash_db_key || '';

    return rules.some(rule => {
        if (!rule.enabled) return false;
        const matchContent = rule.matchContent;
        if (!matchContent) return false;

        switch (rule.category) {
            case 'keyword':
                return messageText.includes(matchContent.toLowerCase());
            case 'attachedMedia':
                // Do not convert to lower case, as MD5 (base64) is case sensitive.
                return messageMd5 === matchContent.replace('md5:', '');
            case 'entireMessage':
                 try {
                    const conditions = JSON.parse(matchContent);
                    const textMatch = conditions.text ? messageText.includes(conditions.text.toLowerCase()) : false;
                    // Do not convert to lower case for media hash
                    const mediaHashInRule = conditions.media ? conditions.media.replace('md5:', '') : null;
                    const mediaMatch = mediaHashInRule ? messageMd5 === mediaHashInRule : false;
                    return textMatch || mediaMatch;
                } catch (e) {
                    // Fallback for old plain text rules
                    const matchContentLower = matchContent.toLowerCase();
                    return messageText.includes(matchContentLower) || (messageMd5 === matchContentLower);
                }
            case 'embeddedLink':
                const urlRegex = /(https?:\/\/[^\s]+)/g;
                let urls;
                while ((urls = urlRegex.exec(message.text || '')) !== null) {
                    if (urls[0].toLowerCase().includes(matchContent.toLowerCase())) {
                        return true;
                    }
                }
                return false;
            default:
                return false;
        }
    });
}

function applyFiltersToMessageContent(message, rules) {
    const modifiedMessage = JSON.parse(JSON.stringify(message));
    let modifiedText = modifiedMessage.text || '';
    let attachmentFiltered = false;

    for (const rule of rules) {
        if (!rule.enabled || rule.action === 'filterOut') {
            continue;
        }

        const matchContent = rule.matchContent;
        const matchContentLower = matchContent.toLowerCase();

        switch (rule.category) {
            case 'keyword':
                if (modifiedText.toLowerCase().includes(matchContentLower)) {
                    if (rule.action === 'remove') {
                        modifiedText = modifiedText.replace(new RegExp(matchContent.replace(/[-\/\\^$*+?.()|[\]{}]/g, '\\$&'), 'gi'), '');
                    } else if (rule.action === 'replace') {
                        modifiedText = modifiedText.replace(new RegExp(matchContent.replace(/[-\/\\^$*+?.()|[\]{}]/g, '\\$&'), 'gi'), rule.replaceContent);
                    }
                }
                break;
            case 'attachedMedia':
                if (modifiedMessage.attachment && modifiedMessage.attachment.filehash_db_key === matchContent.replace('md5:', '')) {
                    if (rule.action === 'remove' || rule.action === 'replace') {
                        attachmentFiltered = true;
                    }
                }
                break;
            case 'embeddedLink':
                const urlRegex = /(https?:\/\/[^\s]+)/g;
                if (rule.action === 'remove') {
                    modifiedText = modifiedText.replace(urlRegex, (url) => {
                        return url.toLowerCase().includes(matchContentLower) ? '' : url;
                    });
                } else if (rule.action === 'replace') {
                    modifiedText = modifiedText.replace(urlRegex, (url) => {
                        return url.toLowerCase().includes(matchContentLower) ? rule.replaceContent : url;
                    });
                }
                break;
            case 'entireMessage':
                try {
                    const conditions = JSON.parse(matchContent);
                    const textToMatch = conditions.text;
                    const mediaToMatch = conditions.media ? conditions.media.replace('md5:', '') : null;

                    const textMatches = textToMatch && modifiedText.toLowerCase().includes(textToMatch.toLowerCase());
                    const mediaMatches = mediaToMatch && modifiedMessage.attachment && modifiedMessage.attachment.filehash_db_key === mediaToMatch;

                    if (textMatches && mediaMatches) { // AND logic for applying filter
                        if (rule.action === 'remove') {
                            modifiedText = modifiedText.replace(new RegExp(textToMatch.replace(/[-\/\\^$*+?.()|[\]{}]/g, '\\$&'), 'gi'), '');
                            attachmentFiltered = true;
                        } else if (rule.action === 'replace') {
                            modifiedText = modifiedText.replace(new RegExp(textToMatch.replace(/[-\/\\^$*+?.()|[\]{}]/g, '\\$&'), 'gi'), rule.replaceContent);
                            attachmentFiltered = true; // Also remove/replace attachment
                        }
                    }
                } catch (e) {
                    // Fallback for old plain text rules
                    if (modifiedText.toLowerCase().includes(matchContentLower)) {
                        if (rule.action === 'remove') {
                            modifiedText = modifiedText.replace(new RegExp(matchContent.replace(/[-\/\\^$*+?.()|[\]{}]/g, '\\$&'), 'gi'), '');
                        } else if (rule.action === 'replace') {
                            modifiedText = modifiedText.replace(new RegExp(matchContent.replace(/[-\/\\^$*+?.()|[\]{}]/g, '\\$&'), 'gi'), rule.replaceContent);
                        }
                    }
                    if (modifiedMessage.attachment && modifiedMessage.attachment.filehash_db_key === matchContentLower) {
                        if (rule.action === 'remove' || rule.action === 'replace') {
                            attachmentFiltered = true;
                        }
                    }
                }
                break;
        }
    }

    modifiedMessage.text = modifiedText;
    if (attachmentFiltered) {
        modifiedMessage.attachment = null;
    }

    return modifiedMessage;
}

    function renderThreadList() {
        const threadDisplayContainer = document.getElementById('otk-thread-display-container');
        if (!threadDisplayContainer) {
            consoleError('Thread display container not found.');
            return;
        }

        threadDisplayContainer.innerHTML = ''; // Clear previous list
        // consoleLog('renderThreadList: Cleared thread display container.'); // Redundant if list is empty

        if (activeThreads.length === 0) {
            consoleLog('renderThreadList: No active threads to display.');
            // Optionally display a message in the GUI like "No active OTK threads."
            // threadDisplayContainer.textContent = "No active OTK threads.";
            return;
        }

    const themeSettings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
    const timePosition = themeSettings.otkThreadTimePosition || 'After Title';

        // Prepare display objects, ensuring messages exist for titles/times
        const threadDisplayObjects = activeThreads.map(threadId => {
            const messages = messagesByThreadId[threadId] || [];
            let title = `Thread ${threadId}`; // Default title
            let firstMessageTime = null;
            let originalThreadUrl = `https://boards.4chan.org/b/thread/${threadId}`;


            if (messages.length > 0 && messages[0]) {
                title = messages[0].title ? toTitleCase(decodeEntities(messages[0].title)) : `Thread ${threadId}`;
                firstMessageTime = messages[0].time;
            } else {
                consoleWarn(`Thread ${threadId} has no messages or messages[0] is undefined for title/time. Using default title.`);
            }


            return {
                id: threadId,
                title: title,
                firstMessageTime: firstMessageTime,
                color: getThreadColor(threadId),
                url: originalThreadUrl
            };
        }).filter(thread => thread.firstMessageTime !== null); // Only display threads with a valid time

        // Sort by most recent first message time
        threadDisplayObjects.sort((a, b) => b.firstMessageTime - a.firstMessageTime);
        consoleLog(`renderThreadList: Prepared ${threadDisplayObjects.length} threads for display:`, threadDisplayObjects.map(t => `${t.id} (${t.title.substring(0,20)}...)`));

        const threadsToDisplayInList = threadDisplayObjects.slice(0, 3);

        threadsToDisplayInList.forEach((thread, index) => {
            const threadItemDiv = document.createElement('div');
            let marginBottom = index < (threadsToDisplayInList.length -1) ? '0px' : '3px';
            threadItemDiv.style.cssText = `
                display: flex;
                align-items: center;
                padding: 4px;
                border-radius: 3px;
                margin-bottom: ${marginBottom};
            `;

            const colorBox = document.createElement('div');
            colorBox.style.cssText = `
                width: 12px;
                height: 12px;
                background-color: ${thread.color};
                border-radius: 2px;
                margin-right: 6px;
                flex-shrink: 0;
                border: var(--otk-gui-thread-box-outline, none);
            `;
            threadItemDiv.appendChild(colorBox);

            const textContentDiv = document.createElement('div');
            textContentDiv.style.display = 'flex';
            textContentDiv.style.flexDirection = 'column';
            textContentDiv.style.maxWidth = 'calc(100% - 18px)'; // Prevent overflow from colorBox

            const titleLink = document.createElement('a');
            titleLink.href = thread.url;
            titleLink.target = '_blank';
            const fullTitle = thread.title;
            titleLink.textContent = truncateTitleWithWordBoundary(fullTitle, 65); // Max length adjusted
            titleLink.title = fullTitle;
            let titleLinkStyle = `
                color: var(--otk-gui-threadlist-title-color);
                text-decoration: none;
                font-weight: bold;
                font-size: 12px;
                margin-bottom: 2px;
                display: block;
                /* width: 100%; */ /* Removed to allow natural width up to container */
                white-space: nowrap;
                overflow: hidden;
                text-overflow: ellipsis;
            `;

            const time = new Date(thread.firstMessageTime * 1000);
            const timeStr = time.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', hour12: false });

            const bracketStyle = themeSettings.otkThreadTimeBracketStyle || '[]';
            const bracketColor = themeSettings.otkThreadTimeBracketColor || 'var(--otk-gui-threadlist-time-color)';

            const timestampSpan = document.createElement('span');
            timestampSpan.style.marginLeft = '5px';

            if (bracketStyle !== 'none') {
                const openBracket = document.createElement('span');
                openBracket.textContent = bracketStyle[0];
                openBracket.style.color = bracketColor;
                timestampSpan.appendChild(openBracket);
            }

            const timeText = document.createElement('span');
            timeText.textContent = timeStr;
            timeText.style.color = 'var(--otk-gui-threadlist-time-color)';
            timeText.style.fontSize = '12px'; // Match title font size
            timestampSpan.appendChild(timeText);

            if (bracketStyle !== 'none') {
                const closeBracket = document.createElement('span');
                closeBracket.textContent = bracketStyle[1];
                closeBracket.style.color = bracketColor;
                timestampSpan.appendChild(closeBracket);
            }

            titleLink.style.cssText = titleLinkStyle;

            titleLink.onmouseover = () => { titleLink.style.textDecoration = 'underline'; };
            titleLink.onmouseout = () => { titleLink.style.textDecoration = 'none'; };

            // Click to open messages in viewer
            titleLink.onclick = (event) => {
                event.preventDefault(); // Prevent default link navigation
                consoleLog(`Thread title clicked: ${thread.id} - ${thread.title}. Ensuring viewer is open and scrolling to message.`);

                if (otkViewer && otkViewer.style.display === 'none') {
                    // toggleViewer will call renderMessagesInViewer
                    toggleViewer();
                } else if (otkViewer) {
                    // If viewer is already open, ensure content is rendered (might be redundant if toggleViewer always renders)
                    // and then scroll. If renderMessagesInViewer is heavy, only call if needed.
                    // For now, let's assume it's okay to call renderMessagesInViewer again to ensure freshness,
                    // or that toggleViewer's render is sufficient if it was just opened.
                    // A more optimized way would be to check if content for this thread ID is visible.
                    if (otkViewer.style.display !== 'block') { // A failsafe if toggleViewer wasn't called
                        otkViewer.style.display = 'block';
                        document.body.style.overflow = 'hidden';
                         renderMessagesInViewer(); // Render if it wasn't made visible by toggleViewer
                    }
                }

                // Attempt to scroll to the message after a brief delay to allow rendering
                setTimeout(() => {
                    const messagesContainer = document.getElementById('otk-messages-container');
                    if (messagesContainer) {
                        // Find the OP message for this thread.
                        // We need a reliable way to identify an OP. Assuming OP's message ID is the thread ID.
                        const opMessageElement = messagesContainer.querySelector(`div[data-message-id="${thread.id}"]`);
                        // A more robust check might be needed if multiple messages could have data-message-id="${thread.id}"
                        // (e.g. if a post quotes the OP)
                        // For now, this assumes the first such element is the one we want, or it's unique enough.

                        if (opMessageElement) {
                            consoleLog(`Scrolling to message element for thread OP ${thread.id}.`);
                            opMessageElement.scrollIntoView({ behavior: 'smooth', block: 'start' });
                            // Highlight briefly? (Optional future enhancement)
                            // opMessageElement.style.outline = '2px solid red';
                            // setTimeout(() => { opMessageElement.style.outline = ''; }, 2000);
                        } else {
                            consoleWarn(`Could not find message element for thread OP ${thread.id} to scroll to.`);
                            // If not found, scroll to top as a fallback, or do nothing.
                            // messagesContainer.scrollTop = 0;
                        }
                    }
                }, 100); // Delay to allow render. May need adjustment.
            };

            const titleTimeContainer = document.createElement('div');
            titleTimeContainer.style.display = 'flex';
            titleTimeContainer.style.alignItems = 'baseline';

            const dividerEnabled = themeSettings.otkThreadTimeDividerEnabled || false;
            const dividerSymbol = themeSettings.otkThreadTimeDividerSymbol || '|';
            const dividerColor = themeSettings.otkThreadTimeDividerColor || '#ffffff';

            if (timePosition === 'Before Title') {
                titleTimeContainer.appendChild(timestampSpan);
            }

            if (dividerEnabled) {
                const dividerSpan = document.createElement('span');
                dividerSpan.textContent = dividerSymbol;
                dividerSpan.style.color = dividerColor;
                dividerSpan.style.fontSize = '10px';
                dividerSpan.style.padding = '0 5px';
                titleTimeContainer.appendChild(dividerSpan);
            }

            titleTimeContainer.appendChild(titleLink);

            if (timePosition === 'After Title') {
                titleTimeContainer.appendChild(timestampSpan);
            }

            const crayonIcon = document.createElement('span');
            crayonIcon.innerHTML = '🖍️';
            crayonIcon.style.cssText = `
                font-size: 12px;
                cursor: pointer;
                margin-left: 8px;
                visibility: hidden;
            `;
            crayonIcon.title = "Reply to this thread";
            titleTimeContainer.appendChild(crayonIcon);

            crayonIcon.addEventListener('click', (e) => {
                e.stopPropagation();
                e.preventDefault();

                const threadUrl = thread.url;
                const popup = window.open(threadUrl, '_blank', 'width=460,height=425,resizable,scrollbars');

                if (popup) {
                    popup.addEventListener('load', () => {
                        const script = popup.document.createElement('script');
                        script.textContent = `
                            const links = Array.from(document.querySelectorAll('a'));
                            const replyLink = links.find(a => a.textContent.trim() === 'Post a Reply');
                            if (replyLink) {
                                replyLink.click();
                            } else {
                                console.log("Could not find 'Post a Reply' link.");
                            }
                        `;
                        popup.document.body.appendChild(script);
                    }, true);
                } else {
                    consoleError("Could not open popup window. Please check your browser's popup blocker settings.");
                }
            });

            const blockIcon = document.createElement('span');
            blockIcon.innerHTML = '&#x2715;'; // A simple 'X' icon
            blockIcon.style.cssText = `
                font-size: 12px;
                color: #ff8080;
                cursor: pointer;
                margin-left: 5px;
                visibility: hidden;
            `;
            blockIcon.title = "Block this thread";
            titleTimeContainer.appendChild(blockIcon);

            threadItemDiv.addEventListener('mouseenter', () => {
                crayonIcon.style.visibility = 'visible';
                blockIcon.style.visibility = 'visible';
            });
            threadItemDiv.addEventListener('mouseleave', () => {
                crayonIcon.style.visibility = 'hidden';
                blockIcon.style.visibility = 'hidden';
            });

            blockIcon.addEventListener('click', (e) => {
                e.stopPropagation();
                e.preventDefault();

                blockedThreads.add(thread.id);
                localStorage.setItem(BLOCKED_THREADS_KEY, JSON.stringify(Array.from(blockedThreads)));

                activeThreads = activeThreads.filter(id => id !== thread.id);
                localStorage.setItem(THREADS_KEY, JSON.stringify(activeThreads));

                if (confirm(`Thread ${thread.id} blocked. Also remove its messages from the viewer?`)) {
                    delete messagesByThreadId[thread.id];
                    // Re-render viewer if it's open
                    if (otkViewer && otkViewer.style.display === 'block') {
                        renderMessagesInViewer();
                    }
                }

                renderThreadList();
        updateDisplayedStatistics(false);
            });

            textContentDiv.appendChild(titleTimeContainer);
            threadItemDiv.appendChild(textContentDiv);
            threadDisplayContainer.appendChild(threadItemDiv);
        });


        if (threadDisplayObjects.length > 3) {
            const numberOfAdditionalThreads = threadDisplayObjects.length - 3;
            const hoverContainer = document.createElement('div');
            hoverContainer.style.cssText = `
                display: inline-block;
                position: relative;
            `;
            const moreIndicator = document.createElement('div');
            moreIndicator.id = 'otk-more-threads-indicator';
            moreIndicator.textContent = `(+${numberOfAdditionalThreads})`;
            moreIndicator.style.cssText = `
                font-size: 12px;
                color: #ccc;
                font-style: italic;
                cursor: pointer;
                padding: 3px 6px;
                margin-left: 8px;
                display: inline;
            `;
            hoverContainer.appendChild(moreIndicator);

            if (threadsToDisplayInList.length > 0) {
                const lastThreadItemDiv = threadDisplayContainer.lastChild;
                const textContentDiv = lastThreadItemDiv?.children[1];
                if (textContentDiv && textContentDiv.firstChild) {
                    const titleTimeContainer = textContentDiv.firstChild;
                    const titleLink = titleTimeContainer.querySelector('a');

                    if (timePosition === 'Before Title') {
                        // When time is before the title, append after the title link.
                        titleLink.parentNode.insertBefore(hoverContainer, titleLink.nextSibling);
                    } else {
                        // When time is after the title, append to the end of the container.
                        titleTimeContainer.appendChild(hoverContainer);
                    }
                }
            } else {
                moreIndicator.style.marginLeft = '0px';
                moreIndicator.style.paddingLeft = '22px';
                threadDisplayContainer.appendChild(hoverContainer);
            }


            let tooltip = null;
            let tooltipTimeout;

            hoverContainer.addEventListener('mouseenter', () => {
                consoleLog('hoverContainer mouseenter: showing tooltip');
                moreIndicator.style.textDecoration = 'underline';
                if (tooltip) {
                    consoleLog('Removing existing tooltip before creating new one');
                    tooltip.remove();
                }

                tooltip = document.createElement('div');
                tooltip.id = 'otk-more-threads-tooltip';
                tooltip.style.cssText = `
                    position: absolute;
                    background-color: #343434; /* New background */
                    border: 1px solid #555;    /* New border */
                    border-radius: 4px;
                    padding: 8px;
                    z-index: 100001; /* Higher than GUI bar */
                    color: #e6e6e6; /* New font color */
                    font-size: 12px;
                    max-width: 340px; /* Accommodate new icons */
                    box-shadow: 0 3px 8px rgba(0,0,0,0.6);
                    pointer-events: auto;
                    display: block;
                    opacity: 1;
                    /* border: 1px solid red; */ /* For debugging visibility */
                `;

                const additionalThreads = threadDisplayObjects.slice(3);
                additionalThreads.forEach(thread => {
                    const tooltipItemDiv = document.createElement('div');
                    tooltipItemDiv.style.cssText = `
                        display: flex;
                        align-items: center;
                        justify-content: space-between;
                        padding: 2px 0;
                    `;

                    const tooltipLink = document.createElement('a');
                    tooltipLink.href = thread.url;
                    tooltipLink.target = '_blank';
                    tooltipLink.textContent = truncateTitleWithWordBoundary(thread.title, 65);
                    tooltipLink.title = thread.title;
                    tooltipLink.style.cssText = `
                        display: inline-block;
                        color: #cccccc;
                        text-decoration: none;
                        white-space: nowrap;
                        overflow: hidden;
                        text-overflow: ellipsis;
                        flex-grow: 1;
                    `;
                    tooltipLink.onmouseover = () => { tooltipLink.style.color = '#e6e6e6'; tooltipLink.style.textDecoration = 'underline';};
                    tooltipLink.onmouseout = () => { tooltipLink.style.color = '#cccccc'; tooltipLink.style.textDecoration = 'none';};

                    tooltipItemDiv.appendChild(tooltipLink);

                    const iconsWrapper = document.createElement('div');
                    iconsWrapper.style.cssText = 'display: flex; align-items: center;';

                    const crayonIcon = document.createElement('span');
                    crayonIcon.innerHTML = '🖍️';
                    crayonIcon.style.cssText = `font-size: 12px; cursor: pointer; margin-left: 8px; visibility: hidden;`;
                    crayonIcon.title = "Reply to this thread";

                    crayonIcon.addEventListener('click', (e) => {
                        e.stopPropagation();
                        e.preventDefault();
                        const threadUrl = thread.url;
                        const popup = window.open(threadUrl, '_blank', 'width=460,height=425,resizable,scrollbars');
                        if (popup) {
                            popup.addEventListener('load', () => {
                                const script = popup.document.createElement('script');
                                script.textContent = `const links = Array.from(document.querySelectorAll('a')); const replyLink = links.find(a => a.textContent.trim() === 'Post a Reply'); if (replyLink) { replyLink.click(); }`;
                                popup.document.body.appendChild(script);
                            }, true);
                        }
                    });

                    const blockIcon = document.createElement('span');
                    blockIcon.innerHTML = '&#x2715;';
                    blockIcon.style.cssText = `font-size: 12px; color: #ff8080; cursor: pointer; margin-left: 5px; visibility: hidden;`;
                    blockIcon.title = "Block this thread";

                    blockIcon.addEventListener('click', (e) => {
                        e.stopPropagation();
                        e.preventDefault();
                        blockedThreads.add(thread.id);
                        localStorage.setItem(BLOCKED_THREADS_KEY, JSON.stringify(Array.from(blockedThreads)));
                        activeThreads = activeThreads.filter(id => id !== thread.id);
                        localStorage.setItem(THREADS_KEY, JSON.stringify(activeThreads));
                        if (confirm(`Thread ${thread.id} blocked. Also remove its messages from the viewer?`)) {
                            delete messagesByThreadId[thread.id];
                            if (otkViewer && otkViewer.style.display === 'block') {
                                renderMessagesInViewer();
                            }
                        }
                        renderThreadList();
                        updateDisplayedStatistics(false);
                    });

                    iconsWrapper.appendChild(crayonIcon);
                    iconsWrapper.appendChild(blockIcon);
                    tooltipItemDiv.appendChild(iconsWrapper);

                    tooltipItemDiv.addEventListener('mouseenter', () => {
                        crayonIcon.style.visibility = 'visible';
                        blockIcon.style.visibility = 'visible';
                    });
                    tooltipItemDiv.addEventListener('mouseleave', () => {
                        crayonIcon.style.visibility = 'hidden';
                        blockIcon.style.visibility = 'hidden';
                    });

                    tooltip.appendChild(tooltipItemDiv);
                });

                document.body.appendChild(tooltip);
                consoleLog('Tooltip appended to body');

                const indicatorRect = moreIndicator.getBoundingClientRect();
                const tooltipRect = tooltip.getBoundingClientRect();

                let leftPos = indicatorRect.left;
                let topPos = indicatorRect.bottom + window.scrollY + 3; // Slightly more offset

                if (leftPos + tooltipRect.width > window.innerWidth - 10) { // 10px buffer
                    leftPos = window.innerWidth - tooltipRect.width - 10;
                }
                if (topPos + tooltipRect.height > window.innerHeight + window.scrollY - 10) {
                    consoleLog('Adjusting tooltip position to above indicator due to bottom overflow');
                    topPos = indicatorRect.top + window.scrollY - tooltipRect.height - 3;
                }
                 if (leftPos < 10) leftPos = 10; // Prevent going off left edge


                tooltip.style.left = `${leftPos}px`;
                tooltip.style.top = `${topPos}px`;
                consoleLog('Tooltip final position:', {left: leftPos, top: topPos});

                tooltip.addEventListener('mouseenter', () => {
                    consoleLog('Tooltip mouseenter: clearing hide timeout');
                    if (tooltipTimeout) clearTimeout(tooltipTimeout);
                });

                tooltip.addEventListener('mouseleave', () => {
                     consoleLog('Tooltip mouseleave: setting hide timeout');
                    tooltipTimeout = setTimeout(() => {
                        if (tooltip && !tooltip.matches(':hover') && !moreIndicator.matches(':hover')) {
                            consoleLog('Hiding tooltip after timeout (left tooltip)');
                            tooltip.remove();
                            tooltip = null;
                        }
                    }, 300);
                });
            });

            hoverContainer.addEventListener('mouseleave', () => {
                consoleLog('hoverContainer mouseleave: setting hide timeout');
                moreIndicator.style.textDecoration = 'none';
                tooltipTimeout = setTimeout(() => {
                    if (tooltip && !tooltip.matches(':hover') && !moreIndicator.matches(':hover')) {
                        consoleLog('Hiding tooltip after timeout (left hoverContainer)');
                        tooltip.remove();
                        tooltip = null;
                    }
                }, 300);
            });
        }
    }

    // Helper function to format timestamp for message headers
    function formatTimestampForHeader(unixTime) {
        const date = new Date(unixTime * 1000);
        const day = String(date.getDate()).padStart(2, '0');
        const month = String(date.getMonth() + 1).padStart(2, '0'); // Months are 0-indexed
        const year = date.getFullYear();
        const hours = String(date.getHours()).padStart(2, '0');
        const minutes = String(date.getMinutes()).padStart(2, '0');
        const seconds = String(date.getSeconds()).padStart(2, '0');
        return {
            time: `${hours}:${minutes}:${seconds}`,
            date: `${day}/${month}/${year}`
        };
    }

    async function renderMessagesInViewer(options = {}) {
    const { isToggleOpen = false } = options;
        if (!otkViewer) {
            consoleError("Viewer element not found, cannot render messages.");
            return;
        }
        const loadingText = isToggleOpen ? "Restoring view..." : "Loading all messages...";
        showLoadingScreen(loadingText);

        // Global sets uniqueImageViewerHashes and uniqueVideoViewerHashes are used directly.
        // No local const declarations needed here.

        // Use a slight delay to ensure the loading screen renders before heavy processing
        await new Promise(resolve => setTimeout(resolve, 50));

        // Revoke old blob URLs before creating new ones
        for (const url of createdBlobUrls) {
            URL.revokeObjectURL(url);
        }
        createdBlobUrls.clear();

        // Clear state for full rebuild (using global sets)
        renderedMessageIdsInViewer.clear();
        uniqueImageViewerHashes.clear(); // Now clearing the global set
        viewerTopLevelAttachedVideoHashes.clear(); // Clear new set for attached videos in top-level messages
        viewerTopLevelEmbedIds.clear(); // Clear new set for embeds in top-level messages
        renderedFullSizeImageHashes.clear(); // Clear for new viewer session
        consoleLog("[renderMessagesInViewer] Cleared renderedMessageIdsInViewer, unique image hashes, top-level video tracking sets, and renderedFullSizeImageHashes for full rebuild.");

        otkViewer.innerHTML = ''; // Clear previous content

        messagesByThreadId = await loadMessagesFromDB();

        let allMessages = getAllMessagesSorted();

    const themeSettings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
    const messageLimitEnabled = themeSettings.otkMessageLimitEnabled !== false;
    if (messageLimitEnabled) {
        const messageLimitValue = parseInt(themeSettings.otkMessageLimitValue || '500', 10);
        consoleLog(`[ViewerPruning] Message limit check: Total messages=${allMessages.length}, Limit=${messageLimitValue}, Enabled=${messageLimitEnabled}`);
        if (allMessages.length > messageLimitValue) {
            consoleLog(`[ViewerPruning] Message limit exceeded. Starting advanced pruning for viewer.`);

            const allMessagesById = new Map(allMessages.map(m => [m.id, m]));
            const newestMessages = allMessages.slice(-messageLimitValue);
            const messagesToKeepIds = new Set(newestMessages.map(m => m.id));
            const quoteRegex = />>(\d+)/g;
            const processingQueue = [...newestMessages];

            consoleLog(`[ViewerPruning] Initial set of newest messages for quote chasing: ${processingQueue.length}`);

            let processedCount = 0;
            const MAX_PROCESSED = processingQueue.length * 5; // Safety break

            while (processingQueue.length > 0) {
                processedCount++;
                if (processedCount > MAX_PROCESSED) {
                    consoleWarn("[ViewerPruning] Exceeded max processing iterations. Breaking quote search to prevent infinite loop.");
                    break;
                }

                const message = processingQueue.shift();
                if (!message || !message.text) continue;

                let match;
                while ((match = quoteRegex.exec(message.text)) !== null) {
                    const quoteId = parseInt(match[1], 10);
                    if (!messagesToKeepIds.has(quoteId)) {
                        messagesToKeepIds.add(quoteId);
                        const quotedMessage = allMessagesById.get(quoteId);
                        if (quotedMessage) {
                            processingQueue.push(quotedMessage);
                        }
                    }
                }
            }
            consoleLog(`[ViewerPruning] Total messages to keep after quote search: ${messagesToKeepIds.size}`);

            allMessages = allMessages.filter(m => messagesToKeepIds.has(m.id));

        // Enforce the hard limit after context-aware quote chasing
        if (allMessages.length > messageLimitValue) {
            consoleLog(`[ViewerPruning] Post-quote-chase count (${allMessages.length}) exceeds limit. Trimming to ${messageLimitValue} newest messages from the context-aware set.`);
            allMessages = allMessages.slice(-messageLimitValue);
        }

            consoleLog(`[ViewerPruning] Pruning complete. Messages to render in viewer: ${allMessages.length}`);
        }
    }
        if (!allMessages || allMessages.length === 0) {
            otkViewer.textContent = 'No messages found to display.'; // User-friendly message
            consoleWarn(`No messages to render in viewer.`);
            updateLoadingProgress(100, "No messages to display.");
            setTimeout(hideLoadingScreen, 500);
            return;
        }

        consoleLog(`Rendering ${allMessages.length} messages in viewer.`);

        // No thread title header needed anymore for continuous view

        const messagesContainer = document.createElement('div');
        messagesContainer.id = 'otk-messages-container';

        messagesContainer.style.cssText = `
            position: absolute;
            top: 0;
            left: 0;
            right: 0;
            bottom: 0;
            overflow-y: auto; /* This container scrolls */
            padding: 10px 25px; /* 10px top/bottom, 25px left/right for content and scrollbar */
            box-sizing: border-box;
            /* width and height are now controlled by absolute positioning */
        `;
        otkViewer.appendChild(messagesContainer);

        // Initialize or re-initialize IntersectionObserver for media within this container
        if (mediaIntersectionObserver) {
            mediaIntersectionObserver.disconnect(); // Clean up previous observer if any
            consoleLog('[LazyLoad] Disconnected previous mediaIntersectionObserver.');
        }
        mediaIntersectionObserver = new IntersectionObserver(handleIntersection, {
            root: messagesContainer,
            rootMargin: '0px 0px 300px 0px',
            threshold: 0.01
        });

        const totalMessagesToRender = allMessages.length;
        let messagesProcessedInViewer = 0;
        let imagesFoundInViewer = 0;
        let videosFoundInViewer = 0;
        const mediaLoadPromises = [];
        const embedWrappers = [];
        const updateInterval = Math.max(1, Math.floor(totalMessagesToRender / 20)); // Update progress roughly 20 times or every message

        for (let i = 0; i < totalMessagesToRender; i++) {
            const message = allMessages[i];

            const boardForLink = message.board || 'b';
            const threadColor = getThreadColor(message.originalThreadId);

            const messageElement = createMessageElementDOM(message, mediaLoadPromises, uniqueImageViewerHashes, boardForLink, true, 0, threadColor, null); // Top-level messages have no parent
            if (messageElement) {
                renderedMessageIdsInViewer.add(message.id);
                messagesContainer.appendChild(messageElement);
                const wrappers = messageElement.querySelectorAll('.otk-youtube-embed-wrapper, .otk-twitch-embed-wrapper, .otk-streamable-embed-wrapper, .otk-tweet-embed-wrapper');
                wrappers.forEach(wrapper => embedWrappers.push(wrapper));
            }

            messagesProcessedInViewer++;

            if (message.attachment) {
                const ext = message.attachment.ext.toLowerCase();
                if (['.jpg', '.jpeg', '.png', '.gif'].includes(ext)) {
                    imagesFoundInViewer++;
                } else if (['.webm', '.mp4'].includes(ext)) {
                    videosFoundInViewer++;
                }
            }

            if (messagesProcessedInViewer % updateInterval === 0 || messagesProcessedInViewer === totalMessagesToRender) {
                let currentProgress = (messagesProcessedInViewer / totalMessagesToRender) * 90; // Up to 90% for this stage
                let detailsStr = `Rendering messages (${messagesProcessedInViewer}/${totalMessagesToRender})...`; // Simplified
                updateLoadingProgress(currentProgress, detailsStr);
            }
        }
        otkViewer.appendChild(messagesContainer);

// After processing all messages, update global viewer counts
consoleLog(`[StatsDebug] Unique image hashes for viewer: ${uniqueImageViewerHashes.size}`, uniqueImageViewerHashes);
// consoleLog(`[StatsDebug] Unique video hashes for viewer: ${uniqueVideoViewerHashes.size}`, uniqueVideoViewerHashes); // Removed due to uniqueVideoViewerHashes being obsolete
// viewerActiveImageCount = uniqueImageViewerHashes.size; // MOVED TO AFTER PROMISES
// viewerActiveVideoCount = uniqueVideoViewerHashes.size; // MOVED TO AFTER PROMISES
// updateDisplayedStatistics(); // Refresh stats display -- MOVED TO AFTER PROMISES

        Promise.all(mediaLoadPromises).then(() => {
            embedWrappers.forEach(wrapper => mediaIntersectionObserver.observe(wrapper));
            consoleLog("All inline media load attempts complete.");
            updateLoadingProgress(95, "Finalizing view...");
    viewerActiveImageCount = uniqueImageViewerHashes.size;
    viewerActiveVideoCount = viewerTopLevelAttachedVideoHashes.size + viewerTopLevelEmbedIds.size;
    consoleLog(`[StatsDebug] Viewer counts updated: Images=${viewerActiveImageCount}, Videos (top-level attached + top-level embed)=${viewerActiveVideoCount}`);
updateDisplayedStatistics(false); // Update stats after all media processing is attempted.

            let anchorScrolled = false;
            const storedAnchoredInstanceId = localStorage.getItem(ANCHORED_MESSAGE_ID_KEY);
            consoleLog("storedAnchoredInstanceId from localStorage:", storedAnchoredInstanceId);

            setTimeout(() => {
                if (storedAnchoredInstanceId) {
                    const anchoredElement = document.getElementById(storedAnchoredInstanceId);
                    consoleLog("anchoredElement from getElementById:", anchoredElement);

                    if (anchoredElement && messagesContainer.contains(anchoredElement)) {
                        try {
                            anchoredElement.scrollIntoView({ behavior: 'auto', block: 'center' });
                            anchorScrolled = true;
                            consoleLog(`Scrolled to anchored message instance: ${storedAnchoredInstanceId}`);
                            if (!anchoredElement.classList.contains(ANCHORED_MESSAGE_CLASS)) {
                                anchoredElement.classList.add(ANCHORED_MESSAGE_CLASS);
                            }
                        } catch (e) {
                            consoleError("Error scrolling to anchored message:", e);
                        }
                    } else {
                        consoleWarn(`Anchored message instance ${storedAnchoredInstanceId} not found. Clearing anchor.`);
                        localStorage.removeItem(ANCHORED_MESSAGE_ID_KEY);
                    }
                }
            }, 500);

            if (!anchorScrolled) {
                if (isToggleOpen && lastViewerScrollTop > 0) {
                    messagesContainer.scrollTop = lastViewerScrollTop;
                    consoleLog(`Restored scroll position to: ${lastViewerScrollTop}`);
                } else if (!storedAnchoredInstanceId) {
                    setTimeout(() => {
                        messagesContainer.scrollTop = messagesContainer.scrollHeight;
                        consoleLog(`No anchored message, scrolling to bottom.`);
                    }, 550);
                }
            }

            updateLoadingProgress(100, "View ready!"); // Update text for 100%
            setTimeout(hideLoadingScreen, 200);
            applyThemeSettings({ forceRerender: false }); // Re-apply theme settings to ensure styles are correct after render
        }).catch(err => {
            consoleError("Error occurred during media loading promises:", err);
            updateLoadingProgress(100, "Error loading some media. View may be incomplete.");
            if (messagesContainer) messagesContainer.scrollTop = messagesContainer.scrollHeight; // Still try to scroll
            setTimeout(hideLoadingScreen, 500);
        });
    }

    async function appendNewMessagesToViewer(newMessages) {
        consoleLog(`[appendNewMessagesToViewer] Called with ${newMessages.length} new messages.`);
        const messagesContainer = document.getElementById('otk-messages-container');
        if (!messagesContainer) {
            consoleError("[appendNewMessagesToViewer] messagesContainer not found. Aborting append.");
            hideLoadingScreen();
            return;
        }

        if (newMessages.length === 0) {
            consoleLog("[appendNewMessagesToViewer] No new messages to append.");
            hideLoadingScreen();
            return;
        }

        const messageElementsBefore = messagesContainer.querySelectorAll('.otk-message-container-main');
        consoleLog(`[AppendLimit] Before append: DOM has ${messageElementsBefore.length} messages. renderedMessageIdsInViewer has ${renderedMessageIdsInViewer.size} IDs.`);

        let anchorInfo = { id: null, offset: 0 };
        const containerRect = messagesContainer.getBoundingClientRect();
        const messageElements = messagesContainer.querySelectorAll('.otk-message-container-main, .otk-message-container-quote-depth-1');
        let anchorElement = null;

        for (const el of messageElements) {
            const elRect = el.getBoundingClientRect();
            if (elRect.bottom > containerRect.top && elRect.top < containerRect.bottom) {
                anchorElement = el;
                break;
            }
        }

        if (anchorElement) {
            anchorInfo.id = anchorElement.id;
            anchorInfo.offset = anchorElement.getBoundingClientRect().top - containerRect.top;
            consoleLog(`[ScrollAnchor] Found anchor: ${anchorInfo.id}, offset: ${anchorInfo.offset}`);
        } else {
            consoleLog('[ScrollAnchor] No visible anchor element found. Will fallback to basic scroll restore.');
        }

        const oldScrollTop = messagesContainer.scrollTop; // Keep as fallback

        const newContentDiv = document.createElement('div');

        const themeSettings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
        const separatorDiv = document.createElement('div');
        const separatorAlignment = themeSettings.otkNewMessagesSeparatorAlignment || 'left';
        separatorDiv.style.borderTop = '2px dashed var(--otk-new-messages-divider-color)';
        separatorDiv.style.margin = '20px 0';
        separatorDiv.style.paddingTop = '10px';
        separatorDiv.style.paddingBottom = '10px';
        separatorDiv.style.color = 'var(--otk-new-messages-font-color)';
        separatorDiv.style.fontSize = 'var(--otk-new-messages-font-size)';
        separatorDiv.style.fontStyle = 'italic';
        separatorDiv.style.width = '100%';
        separatorDiv.style.boxSizing = 'border-box';

        if (separatorAlignment.toLowerCase() === 'center') {
            separatorDiv.style.textAlign = 'center';
            const scrollbarWidth = messagesContainer.offsetWidth - messagesContainer.clientWidth;
            if (scrollbarWidth > 0) {
                separatorDiv.style.position = 'relative';
                separatorDiv.style.left = `${scrollbarWidth / 2}px`;
            }
        } else {
            separatorDiv.style.textAlign = separatorAlignment.toLowerCase();
            separatorDiv.style.paddingLeft = '0px';
        }
        const currentTime = new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', hour12: false });
        separatorDiv.textContent = `--- ${currentTime} : ${newMessages.length} New Messages Loaded ---`;
        newContentDiv.appendChild(separatorDiv);

        const mediaLoadPromises = [];
        const messageLimitEnabled = themeSettings.otkMessageLimitEnabled !== false;
        const messageLimitValue = parseInt(themeSettings.otkMessageLimitValue || '500', 10);

        for (const message of newMessages) {
            const boardForLink = message.board || 'b';
            const threadColor = getThreadColor(message.originalThreadId);
            const messageElement = createMessageElementDOM(message, mediaLoadPromises, uniqueImageViewerHashes, boardForLink, true, 0, threadColor, null);
            if (messageElement) {
                newContentDiv.appendChild(messageElement);
                renderedMessageIdsInViewer.add(message.id);
            }
        }

        messagesContainer.appendChild(newContentDiv);

        const messageElementsAfter = messagesContainer.querySelectorAll('.otk-message-container-main');
        consoleLog(`[AppendLimit] After append: DOM has ${messageElementsAfter.length} messages. renderedMessageIdsInViewer has ${renderedMessageIdsInViewer.size} IDs.`);

        if (messageLimitEnabled) {
            const messageElements = messagesContainer.querySelectorAll('.otk-message-container-main');
            if (messageElements.length > messageLimitValue) {
                const numToRemove = messageElements.length - messageLimitValue;
                consoleLog(`[AppendLimit] Exceeds limit of ${messageLimitValue}. Removing ${numToRemove} oldest messages.`);
                for (let i = 0; i < numToRemove; i++) {
                    const messageToRemove = messageElements[i];
                    const messageId = parseInt(messageToRemove.dataset.messageId, 10);
                    if (!isNaN(messageId)) {
                        renderedMessageIdsInViewer.delete(messageId);
                    }
                    messageToRemove.remove();
                }
                const messageElementsFinal = messagesContainer.querySelectorAll('.otk-message-container-main');
                consoleLog(`[AppendLimit] After removal: DOM has ${messageElementsFinal.length} messages. renderedMessageIdsInViewer has ${renderedMessageIdsInViewer.size} IDs.`);
            }
        }

        Promise.all(mediaLoadPromises).then(async () => {
            hideLoadingScreen();

            if (anchorInfo.id) {
                const elementToScrollTo = document.getElementById(anchorInfo.id);
                if (elementToScrollTo) {
                    const newScrollTop = elementToScrollTo.offsetTop - anchorInfo.offset;
                    messagesContainer.scrollTop = newScrollTop;
                    consoleLog(`[ScrollAnchor] Restored scroll to anchor ${anchorInfo.id}. New scrollTop: ${newScrollTop}`);
                } else {
                    messagesContainer.scrollTop = oldScrollTop;
                    consoleLog(`[ScrollAnchor] Anchor element ${anchorInfo.id} not found. Fell back to old scrollTop.`);
                }
            } else {
                messagesContainer.scrollTop = oldScrollTop;
                consoleLog(`[ScrollAnchor] No anchor found. Fell back to old scrollTop.`);
            }

            viewerActiveImageCount = uniqueImageViewerHashes.size;
            viewerActiveVideoCount = viewerTopLevelAttachedVideoHashes.size + viewerTopLevelEmbedIds.size;
            updateDisplayedStatistics();
        }).catch(err => {
            consoleError("[appendNewMessagesToViewer] Error in media promises:", err);
            hideLoadingScreen();
        });
    }


// Helper function to populate attachmentDiv with media (images/videos)
function _populateAttachmentDivWithMedia(
    attachmentDiv, // The div to append media to
    message,       // The message object
    actualBoardForLink, // Board string for URLs
    mediaLoadPromises,  // Array for async operations
    uniqueImageViewerHashes, // Set for tracking unique images shown
    isTopLevelMessage,     // Boolean, for some media logic (e.g., video stats)
    layoutStyle,           // 'new_design' or 'default', to condition New Design specific logic
    renderedFullSizeImageHashes, // Set for tracking full-size images
    viewerTopLevelAttachedVideoHashes, // Set for video stats
    otkMediaDB // IndexedDB instance
) {
    let resizeIcon;

    const loadImageFromCache = (imgElement, isThumb) => {
        const storeId = isThumb ? message.attachment.localThumbStoreId : message.attachment.localStoreId;
        if (storeId && otkMediaDB) {
            const transaction = otkMediaDB.transaction(['mediaStore'], 'readonly');
            const store = transaction.objectStore('mediaStore');
            const request = store.get(storeId);
            request.onsuccess = (event) => {
                const storedItem = event.target.result;
                if (storedItem && storedItem.blob) {
                    const dataURL = URL.createObjectURL(storedItem.blob);
                    createdBlobUrls.add(dataURL);
                    imgElement.src = dataURL;
                }
            };
        }
    };

    if (!message.attachment || !message.attachment.ext) {
        return;
    }

    const isArchived = !activeThreads.includes(message.originalThreadId);
    const mediaLoadModeSetting = localStorage.getItem('otkMediaLoadMode') || 'source_first';
    const mediaLoadMode = isArchived ? 'cache_only' : mediaLoadModeSetting;
    if (isArchived && mediaLoadModeSetting !== 'cache_only') {
        consoleLog(`[MediaLoad] Message ${message.id} is in archived thread ${message.originalThreadId}. Forcing cache-only mode.`);
    }
    const extLower = message.attachment.ext.toLowerCase();
    const filehash = message.attachment.filehash_db_key || `${message.attachment.tim}${extLower}`;

    if (['.jpg', '.jpeg', '.png', '.gif'].includes(extLower)) {
        // --- IMAGE LOGIC ---
        const fullsizeWidth = message.attachment.w;
        const fullsizeHeight = message.attachment.h;

        let defaultToThumbnail;

        // Determine the viewer's max-height constraint
        const maxHeight = (layoutStyle === 'new_design' || isTopLevelMessage) ? 400 : 350;

        // --- SOLUTION START ---
        // New logic: Show full-size if image is small, panoramic, OR has a tiny thumbnail.
        const tnW = message.attachment.tn_w;
        const aspectRatio = fullsizeWidth / fullsizeHeight;
        if ((fullsizeWidth <= 800 && fullsizeHeight <= 600) || aspectRatio > 3 || tnW < 75) {
            defaultToThumbnail = false; // Show the larger version
        } else {
            defaultToThumbnail = true; // Show the thumbnail for other large images
        }
        // --- SOLUTION END ---

        const img = document.createElement('img');
        img.dataset.filehash = filehash;
        img.dataset.thumbWidth = message.attachment.tn_w;
        img.dataset.thumbHeight = message.attachment.tn_h;
        img.style.cursor = 'pointer';
        img.style.display = 'block';
        img.style.borderRadius = '3px';
        img.style.transform = 'translateZ(0)';
        img.style.backfaceVisibility = 'hidden';
        img.style.userSelect = 'none';

        const hasLocalFull = message.attachment.localStoreId;
        const hasLocalThumb = message.attachment.localThumbStoreId;

        const setImageProperties = (mode) => {
            img.dataset.mode = mode;
            let isThumb = (mode === 'thumb');
            const hasCache = isThumb ? hasLocalThumb : hasLocalFull;

            // Set image dimensions
            if (isThumb) {
                img.style.width = message.attachment.tn_w + 'px';
                img.style.height = message.attachment.tn_h + 'px';
                img.style.maxWidth = '';
                img.style.maxHeight = '';
            } else if (mode === 'full') {
                img.style.maxWidth = '85%';
                img.style.maxHeight = (layoutStyle === 'new_design' || isTopLevelMessage) ? '400px' : '350px';
                img.style.width = 'auto';
                img.style.height = 'auto';
            } else { // 'original'
                img.style.maxWidth = '100%';
                img.style.maxHeight = 'none';
                img.style.width = 'auto';
                img.style.height = 'auto';
            }

            // Set image source based on mode and cache availability
            if (mediaLoadMode === 'cache_only') {
                if (hasCache) {
                    loadImageFromCache(img, isThumb);
                } else {
                    consoleWarn(`Image ${message.attachment.filename} (${mode}) not in cache, and mode is cache-only. Not loading from web.`);
                    // Optionally set a placeholder 'broken image' src
                    img.src = ''; // Or a placeholder image data URL
                }
            } else { // 'source_first' mode
                const webImageUrl = isThumb
                    ? `https://i.4cdn.org/${actualBoardForLink}/${message.attachment.tim}s.jpg`
                    : `https://i.4cdn.org/${actualBoardForLink}/${message.attachment.tim}${message.attachment.ext}`;
                img.src = webImageUrl;
                // The onerror handler will attempt to load from cache if the web request fails.
            }
        };

        mediaLoadPromises.push(new Promise(resolve => {
            img.onload = () => {
                img.style.display = 'block';
                resolve();
            };
            img.onerror = () => {
                loadImageFromCache(img, img.dataset.mode === 'thumb');
                resolve();
            };
        }));

        setImageProperties(defaultToThumbnail ? 'thumb' : 'full');
        uniqueImageViewerHashes.add(filehash);

        img.addEventListener('click', () => {
            const tnW = parseInt(img.dataset.thumbWidth, 10) || 0;
            const tnH = parseInt(img.dataset.thumbHeight, 10) || 0;
            const isTinyThumbnail = tnW < 30 || tnH < 30;
            const currentMode = img.dataset.mode;

            if (isTinyThumbnail) {
                if (currentMode === 'full') {
                    setImageProperties('original');
                } else {
                    setImageProperties('full');
                }
            } else {
                if (currentMode === 'thumb') {
                    setImageProperties('full');
                } else {
                    setImageProperties('thumb');
                }
            }
        });

        const imageWrapper = document.createElement('div');
        imageWrapper.classList.add('image-wrapper');
        imageWrapper.style.position = 'relative';
        imageWrapper.style.display = 'inline-block';
        imageWrapper.style.userSelect = 'none';

        const blurIcon = document.createElement('div');
        blurIcon.classList.add('blur-icon');
        blurIcon.style.cssText = `
            position: absolute;
            top: 5px;
            left: 5px;
            width: 24px;
            height: 24px;
            background-color: var(--otk-blur-icon-bg-color);
            border-radius: 4px;
            cursor: pointer;
            display: none;
            align-items: center;
            justify-content: center;
            z-index: 10;
        `;
        blurIcon.title = 'Toggle blur for this image';

        const blurIconForeground = document.createElement('div');
        blurIconForeground.style.cssText = `
            width: 16px;
            height: 16px;
            background-color: var(--otk-blur-icon-color);
            -webkit-mask-image: url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" height="24px" viewBox="0 -960 960 960" width="24px"><path d="m644-428-58-59q9-47-27-88t-93-32l-58-58q17-8 34.5-12t37.5-4q75 0 127.5 52.5T660-500q0 20-4 37.5T644-428Zm128 126-58-56q38-29 67.5-63.5T832-500q-50-101-143.5-160.5T480-720q-29 0-57 4t-55 12l-62-62q41-17 84-25.5t90-8.5q151 0 269 83.5T920-500q-23 59-60.5 109.5T772-302Zm20 246L624-222q-35 11-70.5 16.5T480-200q-151 0-269-83.5T40-500q21-53 53-98.5t73-81.5L56-792l56-56 736 736-56 56ZM222-624q-29 26-53 57t-41 67q50 101 143.5 160.5T480-280q20 0 39-2.5t39-5.5l-36-38q-11 3-21 4.5t-21 1.5q-75 0-127.5-52.5T300-500q0-11 1.5-21t4.5-21l-84-82Zm319 93Zm-151 75Z"/></svg>');
            mask-image: url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" height="24px" viewBox="0 -960 960 960" width="24px"><path d="m644-428-58-59q9-47-27-88t-93-32l-58-58q17-8 34.5-12t37.5-4q75 0 127.5 52.5T660-500q0 20-4 37.5T644-428Zm128 126-58-56q38-29 67.5-63.5T832-500q-50-101-143.5-160.5T480-720q-29 0-57 4t-55 12l-62-62q41-17 84-25.5t90-8.5q151 0 269 83.5T920-500q-23 59-60.5 109.5T772-302Zm20 246L624-222q-35 11-70.5 16.5T480-200q-151 0-269-83.5T40-500q21-53 53-98.5t73-81.5L56-792l56-56 736 736-56 56ZM222-624q-29 26-53 57t-41 67q50 101 143.5 160.5T480-280q20 0 39-2.5t39-5.5l-36-38q-11 3-21 4.5t-21 1.5q-75 0-127.5-52.5T300-500q0-11 1.5-21t4.5-21l-84-82Zm319 93Zm-151 75Z"/></svg>');
            -webkit-mask-size: contain;
            mask-size: contain;
            -webkit-mask-repeat: no-repeat;
            mask-repeat: no-repeat;
            -webkit-mask-position: center;
            mask-position: center;
        `;
        blurIcon.appendChild(blurIconForeground);

        blurIcon.addEventListener('click', (e) => {
            e.stopPropagation();
            e.preventDefault();
            toggleImageBlur(filehash);
        });

        resizeIcon = document.createElement('div');
        resizeIcon.classList.add('resize-icon');
        resizeIcon.style.cssText = `
            position: absolute;
            top: 5px;
            width: 24px;
            height: 24px;
            background-color: var(--otk-resize-icon-bg-color);
            border-radius: 4px;
            cursor: pointer;
            display: none;
            align-items: center;
            justify-content: center;
            z-index: 10;
        `;
        resizeIcon.title = 'Toggle full size';

        const resizeIconForeground = document.createElement('div');
        resizeIconForeground.style.cssText = `
            width: 16px;
            height: 16px;
            background-color: var(--otk-resize-icon-color);
            -webkit-mask-image: url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="16 4 20 4 20 8"></polyline><line x1="20" y1="4" x2="14" y2="10"></line><polyline points="8 20 4 20 4 16"></polyline><line x1="4" y1="20" x2="10" y2="14"></line></svg>');
            mask-image: url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="16 4 20 4 20 8"></polyline><line x1="20" y1="4" x2="14" y2="10"></line><polyline points="8 20 4 20 4 16"></polyline><line x1="4" y1="20" x2="10" y2="14"></line></svg>');
            -webkit-mask-size: contain;
            mask-size: contain;
            -webkit-mask-repeat: no-repeat;
            mask-repeat: no-repeat;
            -webkit-mask-position: center;
            mask-position: center;
        `;
        resizeIcon.appendChild(resizeIconForeground);

        resizeIcon.addEventListener('click', (e) => {
            e.stopPropagation();
            e.preventDefault();
            const currentMode = img.dataset.mode;
            if (currentMode === 'original') {
                const previousMode = img.dataset.previousMode || (defaultToThumbnail ? 'thumb' : 'full');
                setImageProperties(previousMode);
            } else {
                img.dataset.previousMode = currentMode;
                setImageProperties('original');
            }
        });

        imageWrapper.addEventListener('mouseenter', () => {
            blurIcon.style.display = 'flex';
            resizeIcon.style.display = 'flex';
        });
        imageWrapper.addEventListener('mouseleave', () => {
            blurIcon.style.display = 'none';
            resizeIcon.style.display = 'none';
        });

        const blurAmount = (localStorage.getItem(IMAGE_BLUR_AMOUNT_KEY) || 60) / 5;
        if (blurredImages.has(filehash)) {
            img.style.filter = `blur(${blurAmount}px)`;
        }

        imageWrapper.appendChild(img);
        imageWrapper.appendChild(blurIcon);
        imageWrapper.appendChild(resizeIcon);
        attachmentDiv.appendChild(imageWrapper);

        const observer = new MutationObserver(updateIconPositions);

        function updateIconPositions() {
            observer.disconnect();
            if (!resizeIcon || !img.isConnected) return;
            const iconWidth = 24;
            const offset = 5;
            const imageWidth = img.offsetWidth;
            if (imageWidth > 0) {
                resizeIcon.style.top = offset + 'px';
                resizeIcon.style.left = (imageWidth - iconWidth - offset) + 'px';
                resizeIcon.style.right = 'auto';
            }
            observer.observe(img, { attributes: true, attributeFilter: ['style', 'src'] });
        }

        observer.observe(img, { attributes: true, attributeFilter: ['style', 'src'] });
        img.addEventListener('load', updateIconPositions);

    } else if (extLower.endsWith('webm') || extLower.endsWith('mp4')) {
        const videoWrapper = document.createElement('div');
        videoWrapper.classList.add('video-wrapper');
        videoWrapper.style.position = 'relative';
        videoWrapper.style.display = 'inline-block';
        videoWrapper.style.userSelect = 'none';

        const videoElement = document.createElement('video');
        videoElement.controls = true;
        videoElement.style.maxWidth = '85%';
        const defaultMaxHeight = isTopLevelMessage ? '400px' : '300px';
        videoElement.style.maxHeight = defaultMaxHeight;
        videoElement.dataset.defaultMaxHeight = defaultMaxHeight;
        videoElement.style.borderRadius = '3px';
        videoElement.style.display = 'block';

        const loadFromCache = () => {
            if (message.attachment.localStoreId && otkMediaDB) {
                const transaction = otkMediaDB.transaction(['mediaStore'], 'readonly');
                const store = transaction.objectStore('mediaStore');
                const request = store.get(message.attachment.localStoreId);
                request.onsuccess = (event) => {
                    const storedItem = event.target.result;
                    if (storedItem && storedItem.blob) {
                        const dataURL = URL.createObjectURL(storedItem.blob);
                        createdBlobUrls.add(dataURL);
                        videoElement.src = dataURL;
                    } else {
                        consoleWarn(`Video ${message.attachment.filename} not found in cache despite having a localStoreId.`);
                    }
                };
                request.onerror = (event) => {
                    consoleError("Error reading video from cache:", event.target.error);
                };
            } else {
                 consoleWarn(`Video ${message.attachment.filename} has no localStoreId for cache lookup.`);
            }
        };

        videoElement.onerror = () => {
            consoleWarn(`Failed to load video from web source. Falling back to cache for ${message.attachment.filename}.`);
            loadFromCache();
        };

        if (mediaLoadMode === 'cache_only') {
            if (message.attachment.localStoreId) {
                loadFromCache();
            } else {
                consoleWarn(`Video ${message.attachment.filename} not in cache, and mode is cache-only. Not loading from web.`);
                // Optional: You could set a placeholder 'broken video' src here
            }
        } else { // 'source_first' mode
            const webVideoSrc = `https://i.4cdn.org/${actualBoardForLink}/${message.attachment.tim}${extLower.startsWith('.') ? extLower : '.' + extLower}`;
            videoElement.src = webVideoSrc;
        }

        const resizeIcon = document.createElement('div');
        resizeIcon.classList.add('resize-icon');
        resizeIcon.style.cssText = `
            position: absolute;
            top: 5px;
            width: 24px;
            height: 24px;
            background-color: var(--otk-resize-icon-bg-color);
            border-radius: 4px;
            cursor: pointer;
            display: none;
            align-items: center;
            justify-content: center;
            z-index: 10;
        `;
        resizeIcon.title = 'Toggle full size';
        const resizeIconForeground = document.createElement('div');
        resizeIconForeground.style.cssText = `
            width: 16px;
            height: 16px;
            background-color: var(--otk-resize-icon-color);
            -webkit-mask-image: url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="16 4 20 4 20 8"></polyline><line x1="20" y1="4" x2="14" y2="10"></line><polyline points="8 20 4 20 4 16"></polyline><line x1="4" y1="20" x2="10" y2="14"></line></svg>');
            mask-image: url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="16 4 20 4 20 8"></polyline><line x1="20" y1="4" x2="14" y2="10"></line><polyline points="8 20 4 20 4 16"></polyline><line x1="4" y1="20" x2="10" y2="14"></line></svg>');
            -webkit-mask-size: contain;
            mask-size: contain;
            -webkit-mask-repeat: no-repeat;
            mask-repeat: no-repeat;
            -webkit-mask-position: center;
            mask-position: center;
        `;
        resizeIcon.appendChild(resizeIconForeground);

        resizeIcon.addEventListener('click', (e) => {
            e.stopPropagation();
            e.preventDefault();
            if (videoElement.style.maxHeight === 'none') {
                videoElement.style.maxHeight = videoElement.dataset.defaultMaxHeight;
            } else {
                videoElement.style.maxHeight = 'none';
            }
        });

        videoWrapper.addEventListener('mouseenter', () => {
            resizeIcon.style.display = 'flex';
        });
        videoWrapper.addEventListener('mouseleave', () => {
            resizeIcon.style.display = 'none';
        });

        videoWrapper.appendChild(videoElement);
        videoWrapper.appendChild(resizeIcon);
        attachmentDiv.appendChild(videoWrapper);

        const observer = new MutationObserver(updateVideoIconPosition);
        function updateVideoIconPosition() {
            observer.disconnect();
            if (!resizeIcon || !videoElement.isConnected) return;
            const iconWidth = 24;
            const offset = 5;
            const videoWidth = videoElement.offsetWidth;
            if (videoWidth > 0) {
                resizeIcon.style.top = offset + 'px';
                resizeIcon.style.left = (videoWidth - iconWidth - offset) + 'px';
                resizeIcon.style.right = 'auto';
            }
            observer.observe(videoElement, { attributes: true, attributeFilter: ['style', 'src'] });
        }
        observer.observe(videoElement, { attributes: true, attributeFilter: ['style', 'src'] });
        videoElement.addEventListener('loadeddata', updateVideoIconPosition);

        if (message.attachment.filehash_db_key && isTopLevelMessage) {
            viewerTopLevelAttachedVideoHashes.add(message.attachment.filehash_db_key);
        }
    }
}

function wrapInCollapsibleContainer(elementsToWrap) {
    const container = document.createElement('div');
    container.className = 'otk-collapsible-container';

    const placeholder = document.createElement('div');
    placeholder.className = 'otk-collapsible-placeholder';
    placeholder.innerHTML = '<span style="margin-right: 5px;">[+]</span>Blocked Content';
    placeholder.style.cursor = 'pointer';
    placeholder.style.color = 'var(--otk-blocked-content-font-color)';
    placeholder.style.fontSize = '12px';
    placeholder.style.fontStyle = 'italic';
    placeholder.style.padding = '5px 0';

    const contentDiv = document.createElement('div');
    contentDiv.className = 'otk-collapsible-content';
    contentDiv.style.display = 'none';

    elementsToWrap.forEach(el => {
        if (el) {
            contentDiv.appendChild(el);
        }
    });

    placeholder.addEventListener('click', (e) => {
        e.stopPropagation();
        const isHidden = contentDiv.style.display === 'none';
        contentDiv.style.display = isHidden ? 'block' : 'none';
        placeholder.querySelector('span').textContent = isHidden ? '[-]' : '[+]';
    });

    container.appendChild(placeholder);
    container.appendChild(contentDiv);

    return container;
}

function _populateMessageBody(message, mediaLoadPromises, uniqueImageViewerHashes, boardForLink, isTopLevelMessage, currentDepth, threadColor, parentMessageId, ancestors, allThemeSettings, shouldDisplayFilenames, shouldDisableUnderline) {
    const textElement = document.createElement('div');
    textElement.style.whiteSpace = 'pre-wrap';
    textElement.style.overflowWrap = 'break-word';
    textElement.style.wordBreak = 'normal';

    if (shouldDisableUnderline) {
        textElement.style.marginTop = '0px';
        textElement.style.paddingTop = '0px';
    }

    if (message.text && typeof message.text === 'string') {
        const lines = message.text.split('\n');
        const quoteRegex = /^>>(\d+)/;
        const inlineQuoteRegex = />>(\d+)/;

        lines.forEach((line, lineIndex) => {
            const trimmedLine = line.trim();
            // const isBlockQuote = trimmedLine.match(quoteRegex) && trimmedLine.match(quoteRegex)[0] === trimmedLine;
            // The isBlockQuote check was removed as it prevented quote links at max depth from being rendered as text.
            // The logic now falls through to the inline quote handler which correctly processes them.

            let processedAsEmbed = false;
            let soleUrlEmbedMade = false;

            const youtubePatterns = [
                { regex: /^(?:https?:\/\/)?(?:www\.)?youtube\.com\/watch\?(?=.*v=([a-zA-Z0-9_-]+))(?:[?&%#\w\-=\.\/;:]+)+$/, idGroup: 1 },
                { regex: /^(?:https?:\/\/)?(?:www\.)?youtube\.com\/shorts\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?$/, idGroup: 1 },
                { regex: /^(?:https?:\/\/)?youtu\.be\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?$/, idGroup: 1 }
            ];
            const youtubeTimestampRegex = /[?&]t=([0-9hm_s]+)/;
            const inlineYoutubePatterns = [
                { type: 'watch', regex: /(?:https?:\/\/)?(?:www\.)?youtube\.com\/watch\?(?:[^#&?\s]*&)*v=([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;]*)?/, idGroup: 1 },
                { type: 'short', regex: /(?:https?:\/\/)?(?:www\.)?youtube\.com\/shorts\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;]*)?/, idGroup: 1 },
                { type: 'youtu.be', regex: /(?:https?:\/\/)?youtu\.be\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;]*)?/, idGroup: 1 }
            ];
            const twitchPatterns = [
                { type: 'clip_direct', regex: /^(?:https?:\/\/)?clips\.twitch\.tv\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?$/, idGroup: 1 },
                { type: 'clip_channel', regex: /^(?:https?:\/\/)?(?:www\.)?twitch\.tv\/[a-zA-Z0-9_]+\/clip\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?$/, idGroup: 1 },
                { type: 'vod', regex: /^(?:https?:\/\/)?(?:www\.)?twitch\.tv\/(?:videos|v)\/(\d+)(?:[?&%#\w\-=\.\/;:]*)?$/, idGroup: 1 }
            ];
            const twitchTimestampRegex = /[?&]t=((?:\d+h)?(?:\d+m)?(?:\d+s)?)/;
            const inlineTwitchPatterns = [
                { type: 'clip_direct', regex: /(?:https?:\/\/)?clips\.twitch\.tv\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?/, idGroup: 1 },
                { type: 'clip_channel', regex: /(?:https?:\/\/)?(?:www\.)?twitch\.tv\/[a-zA-Z0-9_]+\/clip\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?/, idGroup: 1 },
                { type: 'vod', regex: /(?:https?:\/\/)?(?:www\.)?twitch\.tv\/(?:videos|v)\/(\d+)(?:[?&%#\w\-=\.\/;:]*)?/, idGroup: 1 }
            ];
            const streamablePatterns = [
                { type: 'video', regex: /^(?:https?:\/\/)?streamable\.com\/([a-zA-Z0-9]+)(?:[?#][^\s]*)?$/, idGroup: 1 }
            ];
            const inlineStreamablePatterns = [
                { type: 'video', regex: /(?:https?:\/\/)?streamable\.com\/([a-zA-Z0-9]+)(?:[?&%#\w\-=\.\/;:]*)?/, idGroup: 1 }
            ];
            const tiktokPatterns = [
                { type: 'video', regex: /^(?:https?:\/\/)?(?:www\.)?tiktok\.com\/@[\w.-]+\/video\/(\d+)/, idGroup: 1 }
            ];
            const inlineTiktokPatterns = [
                { type: 'video', regex: /(?:https?:\/\/)?(?:www\.)?tiktok\.com\/@[\w.-]+\/video\/(\d+)/, idGroup: 1 }
            ];
            const kickPatterns = [
                { type: 'clip', regex: /^(?:https?:\/\/)?kick\.com\/[\w.-]+\?clip=([\w-]+)/, idGroup: 1 }
            ];
            const inlineKickPatterns = [
                { type: 'clip', regex: /(?:https?:\/\/)?kick\.com\/[\w.-]+\?clip=([\w-]+)/, idGroup: 1 }
            ];

            if (!soleUrlEmbedMade) {
                for (const patternObj of youtubePatterns) {
                    const match = trimmedLine.match(patternObj.regex);
                    if (match) {
                        const videoId = match[patternObj.idGroup];
                        let timestampStr = null;
                        const timeMatch = trimmedLine.match(youtubeTimestampRegex);
                        if (timeMatch && timeMatch[1]) timestampStr = timeMatch[1];
                        if (videoId) {
                            textElement.appendChild(createYouTubeEmbedElement(videoId, timestampStr));
                            soleUrlEmbedMade = true;
                            processedAsEmbed = true;
                            break;
                        }
                    }
                }
            }
            if (!soleUrlEmbedMade) {
                for (const patternObj of twitchPatterns) {
                    const match = trimmedLine.match(patternObj.regex);
                    if (match) {
                        const id = match[patternObj.idGroup];
                        let timestampStr = null;
                        if (patternObj.type === 'vod') {
                            const timeMatch = trimmedLine.match(twitchTimestampRegex);
                            if (timeMatch && timeMatch[1]) timestampStr = timeMatch[1];
                        }
                        if (id) {
                            textElement.appendChild(createTwitchEmbedElement(patternObj.type, id, timestampStr));
                            soleUrlEmbedMade = true;
                            processedAsEmbed = true;
                            break;
                        }
                    }
                }
            }
            if (!soleUrlEmbedMade) {
                for (const patternObj of tiktokPatterns) {
                    const match = trimmedLine.match(patternObj.regex);
                    if (match) {
                        const videoId = match[patternObj.idGroup];
                        if (videoId) {
                            textElement.appendChild(createTikTokEmbedElement(videoId));
                            soleUrlEmbedMade = true;
                            processedAsEmbed = true;
                            break;
                        }
                    }
                }
            }
            if (!soleUrlEmbedMade) {
                for (const patternObj of streamablePatterns) {
                    const match = trimmedLine.match(patternObj.regex);
                    if (match) {
                        const videoId = match[patternObj.idGroup];
                        if (videoId) {
                            textElement.appendChild(createStreamableEmbedElement(videoId));
                            soleUrlEmbedMade = true;
                            processedAsEmbed = true;
                            break;
                        }
                    }
                }
            }

            if (!soleUrlEmbedMade) {
                let currentTextSegment = line;
                while (currentTextSegment.length > 0) {
                    let earliestMatch = null;
                    let earliestMatchPattern = null;
                    let earliestMatchType = null;
                    let earliestMatchIsQuoteLink = false;

                    for (const patternObj of [...inlineYoutubePatterns, ...inlineKickPatterns, ...inlineTiktokPatterns, ...inlineTwitchPatterns, ...inlineStreamablePatterns]) {
                        const matchAttempt = currentTextSegment.match(patternObj.regex);
                        if (matchAttempt && (earliestMatch === null || matchAttempt.index < earliestMatch.index)) {
                            earliestMatch = matchAttempt;
                            earliestMatchPattern = patternObj;
                            if (inlineYoutubePatterns.includes(patternObj)) earliestMatchType = 'youtube';
                            else if (inlineKickPatterns.includes(patternObj)) earliestMatchType = 'kick';
                            else if (inlineTiktokPatterns.includes(patternObj)) earliestMatchType = 'tiktok';
                            else if (inlineTwitchPatterns.includes(patternObj)) earliestMatchType = 'twitch';
                            else if (inlineStreamablePatterns.includes(patternObj)) earliestMatchType = 'streamable';
                            earliestMatchIsQuoteLink = false;
                        }
                    }

                    const quoteLinkMatch = currentTextSegment.match(inlineQuoteRegex);
                    if (quoteLinkMatch && (earliestMatch === null || quoteLinkMatch.index < earliestMatch.index)) {
                        earliestMatch = quoteLinkMatch;
                        earliestMatchType = null;
                        earliestMatchIsQuoteLink = true;
                    }

                    if (earliestMatch) {
                        processedAsEmbed = true;
                        if (earliestMatch.index > 0) {
                            textElement.appendChild(document.createTextNode(currentTextSegment.substring(0, earliestMatch.index)));
                        }
                        const matchedText = earliestMatch[0];
                        if (earliestMatchIsQuoteLink) {
                            if (currentDepth >= MAX_QUOTE_DEPTH) {
                                textElement.appendChild(document.createTextNode(matchedText));
                            } else {
                                const quotedMessageId = earliestMatch[1];
                                let quotedMessageObject = null;
                                for (const threadIdKey in messagesByThreadId) {
                                    if (messagesByThreadId.hasOwnProperty(threadIdKey)) {
                                        const foundMsg = messagesByThreadId[threadIdKey].find(m => m.id === Number(quotedMessageId));
                                        if (foundMsg) {
                                            quotedMessageObject = foundMsg;
                                            break;
                                        }
                                    }
                                }
                                if (quotedMessageObject) {
                                    const quotedElement = createMessageElementDOM(quotedMessageObject, mediaLoadPromises, uniqueImageViewerHashes, quotedMessageObject.board || boardForLink, false, currentDepth + 1, null, message.id, ancestors);
                                    if (quotedElement) {
                                        textElement.appendChild(quotedElement);
                                    }
                                } else {
                                    const notFoundSpan = document.createElement('span');
                                    notFoundSpan.textContent = `>>${quotedMessageId} (Not Found)`;
                                    notFoundSpan.style.color = '#88ccee';
                                    notFoundSpan.style.textDecoration = 'underline';
                                    textElement.appendChild(notFoundSpan);
                                }
                            }
                        } else {
                            const id = earliestMatch[earliestMatchPattern.idGroup];
                            let timestampStr = null;
                            let embedElement = null;
                            if (earliestMatchType === 'youtube') {
                                const timeMatchInUrl = matchedText.match(youtubeTimestampRegex);
                                if (timeMatchInUrl && timeMatchInUrl[1]) timestampStr = timeMatchInUrl[1];
                                embedElement = createYouTubeEmbedElement(id, timestampStr);
                            } else if (earliestMatchType === 'twitch') {
                                if (earliestMatchPattern.type === 'vod') {
                                    const timeMatchInUrl = matchedText.match(twitchTimestampRegex);
                                    if (timeMatchInUrl && timeMatchInUrl[1]) timestampStr = timeMatchInUrl[1];
                                }
                                embedElement = createTwitchEmbedElement(earliestMatchPattern.type, id, timestampStr);
                            } else if (earliestMatchType === 'streamable') {
                                embedElement = createStreamableEmbedElement(id);
                            } else if (earliestMatchType === 'tiktok') {
                                embedElement = createTikTokEmbedElement(id);
                            } else if (earliestMatchType === 'kick') {
                                embedElement = createKickEmbedElement(id);
                            }
                            if (embedElement) {
                                textElement.appendChild(embedElement);
                            }
                        }
                        currentTextSegment = currentTextSegment.substring(earliestMatch.index + matchedText.length);
                    } else {
                        if (currentTextSegment.length > 0) {
                            if (textElement.lastChild && textElement.lastChild.nodeType === 1 && textElement.lastChild.tagName !== 'BR' && !/^\s/.test(currentTextSegment)) {
                                textElement.appendChild(document.createTextNode(' '));
                            }
                            textElement.appendChild(document.createTextNode(currentTextSegment));
                        }
                        currentTextSegment = "";
                    }
                }
            }
            if (lineIndex < lines.length - 1 && (trimmedLine.length > 0 || processedAsEmbed)) {
                textElement.appendChild(document.createElement('br'));
            }
        });
    } else {
        textElement.textContent = message.text || '';
    }

    if (shouldDisableUnderline && textElement.firstChild && textElement.firstChild.nodeName === 'BR') {
        textElement.removeChild(textElement.firstChild);
    }

    let attachmentDiv = null;
    if (message.attachment && message.attachment.tim) {
        const actualBoardForLink = boardForLink || message.board || 'b';
        attachmentDiv = document.createElement('div');
        attachmentDiv.style.marginTop = '10px';

        if (shouldDisplayFilenames) {
            const filenameLink = document.createElement('a');
            filenameLink.textContent = `${message.attachment.filename} (${message.attachment.ext.substring(1)})`;
            filenameLink.href = `https://i.4cdn.org/${actualBoardForLink}/${message.attachment.tim}${message.attachment.ext}`;
            filenameLink.target = "_blank";
            filenameLink.style.cssText = "color: #60a5fa; display: block; margin-bottom: 5px; text-decoration: underline;";
            attachmentDiv.appendChild(filenameLink);
        }

        _populateAttachmentDivWithMedia(
            attachmentDiv, message, actualBoardForLink, mediaLoadPromises,
            uniqueImageViewerHashes, isTopLevelMessage, 'default',
            renderedFullSizeImageHashes, viewerTopLevelAttachedVideoHashes, otkMediaDB
        );
    }

    return [textElement, attachmentDiv];
}
    // Signature now includes parentMessageId and ancestors
function createMessageElementDOM(message, mediaLoadPromises, uniqueImageViewerHashes, boardForLink, isTopLevelMessage, currentDepth, threadColor, parentMessageId = null, ancestors = new Set(), visualDepth = null) {
        const filterRules = JSON.parse(localStorage.getItem(FILTER_RULES_V2_KEY) || '[]');

        const shouldBeFilteredOut = isMessageFiltered(message, filterRules);
        if (shouldBeFilteredOut) {
            if (!(currentDepth === 0 && message.text && message.text.includes('>>'))) {
                consoleLog(`[Filter] Filtering out message ${message.id} due to a 'filterOut' rule.`);
                return null;
            }
        }

        const processedMessage = applyFiltersToMessageContent(message, filterRules);
        const isFiltered = shouldBeFilteredOut || doesAnyRuleMatch(message, filterRules);

        // const layoutStyle = localStorage.getItem('otkMessageLayoutStyle') || 'default';

        // Stack overflow prevention: Check for circular references.
        if (ancestors.has(message.id)) {
            consoleWarn(`[CircularRef] Circular reference detected for message ID ${message.id}. Aborting render for this branch.`);
            const circularRefSpan = document.createElement('span');
            circularRefSpan.textContent = `>>${message.id} (Circular Reference Detected)`;
            circularRefSpan.style.color = '#ff6b6b';
            return circularRefSpan;
        }

        // Add current message ID to the set of ancestors for the recursive calls.
        const newAncestors = new Set(ancestors).add(message.id);

        let seenEmbeds = [];
        try {
            seenEmbeds = JSON.parse(localStorage.getItem(SEEN_EMBED_URL_IDS_KEY)) || [];
        } catch (e) {
            consoleError("Error parsing seen embeds from localStorage:", e);
        }
        let allThemeSettings = {};
        try {
            allThemeSettings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
        } catch (e) {
            consoleError("Error parsing theme settings from localStorage:", e);
        }

    let effectiveDepthForStyling = currentDepth;
    if (visualDepth !== null) {
        effectiveDepthForStyling = visualDepth;
    }
    const isEvenDepth = effectiveDepthForStyling % 2 === 0;

    const parity = isEvenDepth ? 'Odd' : 'Even';
    const contentFontSizeVar = `var(--otk-msg-depth-${parity.toLowerCase()}-content-font-size)`;
    const backgroundColorVar = `var(--otk-msg-depth-${parity.toLowerCase()}-bg-color)`;
    const textColorVar = `var(--otk-msg-depth-${parity.toLowerCase()}-text-color)`;
    const headerTextColorVar = `var(--otk-msg-depth-${parity.toLowerCase()}-header-text-color)`;
    const headerBorderVar = `var(--otk-viewer-header-border-color-${parity.toLowerCase()})`;

    const shouldDisableUnderline = !isTopLevelMessage;

        const showFilenameKey = isEvenDepth ? 'showOddMessageFilename' : 'showEvenMessageFilename';
        const shouldDisplayFilenames = allThemeSettings[showFilenameKey] === true; // Defaults to false if not set

        // --- Define all media patterns once at the top of the function ---
        const youtubePatterns = [
            { regex: /^(?:https?:\/\/)?(?:www\.)?youtube\.com\/watch\?(?=.*v=([a-zA-Z0-9_-]+))(?:[?&%#\w\-=\.\/;:]+)+$/, idGroup: 1 },
            { regex: /^(?:https?:\/\/)?(?:www\.)?youtube\.com\/shorts\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?$/, idGroup: 1 },
            { regex: /^(?:https?:\/\/)?youtu\.be\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?$/, idGroup: 1 }
        ];
        const youtubeTimestampRegex = /[?&]t=([0-9hm_s]+)/;
        const inlineYoutubePatterns = [
            { type: 'watch', regex: /(?:https?:\/\/)?(?:www\.)?youtube\.com\/watch\?(?:[^#&?\s]*&)*v=([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;]*)?/, idGroup: 1 },
            { type: 'short', regex: /(?:https?:\/\/)?(?:www\.)?youtube\.com\/shorts\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;]*)?/, idGroup: 1 },
            { type: 'youtu.be', regex: /(?:https?:\/\/)?youtu\.be\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;]*)?/, idGroup: 1 }
        ];

        const twitchPatterns = [
            { type: 'clip_direct', regex: /^(?:https?:\/\/)?clips\.twitch\.tv\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?$/, idGroup: 1 },
            { type: 'clip_channel', regex: /^(?:https?:\/\/)?(?:www\.)?twitch\.tv\/[a-zA-Z0-9_]+\/clip\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?$/, idGroup: 1 },
            { type: 'vod', regex: /^(?:https?:\/\/)?(?:www\.)?twitch\.tv\/(?:videos|v)\/(\d+)(?:[?&%#\w\-=\.\/;:]*)?$/, idGroup: 1 }
        ];
        const twitchTimestampRegex = /[?&]t=((?:\d+h)?(?:\d+m)?(?:\d+s)?)/;
        const inlineTwitchPatterns = [
            { type: 'clip_direct', regex: /(?:https?:\/\/)?clips\.twitch\.tv\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?/, idGroup: 1 },
            { type: 'clip_channel', regex: /(?:https?:\/\/)?(?:www\.)?twitch\.tv\/[a-zA-Z0-9_]+\/clip\/([a-zA-Z0-9_-]+)(?:[?&%#\w\-=\.\/;:]*)?/, idGroup: 1 },
            { type: 'vod', regex: /(?:https?:\/\/)?(?:www\.)?twitch\.tv\/(?:videos|v)\/(\d+)(?:[?&%#\w\-=\.\/;:]*)?/, idGroup: 1 }
        ];

        const streamablePatterns = [
            { type: 'video', regex: /^(?:https?:\/\/)?streamable\.com\/([a-zA-Z0-9]+)(?:[?#][^\s]*)?$/, idGroup: 1 }
        ];
        const inlineStreamablePatterns = [
            { type: 'video', regex: /(?:https?:\/\/)?streamable\.com\/([a-zA-Z0-9]+)(?:[?&%#\w\-=\.\/;:]*)?/, idGroup: 1 }
        ];
        const tiktokPatterns = [
            { type: 'video', regex: /^(?:https?:\/\/)?(?:www\.)?tiktok\.com\/@[\w.-]+\/video\/(\d+)/, idGroup: 1 }
        ];
        const inlineTiktokPatterns = [
            { type: 'video', regex: /(?:https?:\/\/)?(?:www\.)?tiktok\.com\/@[\w.-]+\/video\/(\d+)/, idGroup: 1 }
        ];
        const kickPatterns = [
            { type: 'clip', regex: /^(?:https?:\/\/)?kick\.com\/[\w.-]+\?clip=([\w-]+)/, idGroup: 1 }
        ];
        const inlineKickPatterns = [
            { type: 'clip', regex: /(?:https?:\/\/)?kick\.com\/[\w.-]+\?clip=([\w-]+)/, idGroup: 1 }
        ];
        // --- End of media pattern definitions ---

        { // layoutStyle === 'default' or unknown (original logic)
            const messageDiv = document.createElement('div');
            messageDiv.setAttribute('data-message-id', message.id);
            if (visualDepth !== null) {
                messageDiv.dataset.visualDepth = visualDepth;
            }
            if (isTopLevelMessage) {
                messageDiv.classList.add('otk-message-container-main');
            }

            let marginLeft = '0';
            let paddingLeft = '10px'; // Default to 10px
            let marginTop = '15px'; // Default top margin
            let marginBottom = '15px'; // Default bottom margin

            if (!isTopLevelMessage) { // Quoted messages
                marginLeft = '0px';
                marginTop = '10px';
                marginBottom = '0px';
            }

    messageDiv.style.cssText = `
        box-sizing: border-box;
        display: block;
        background-color: ${backgroundColorVar};
        color: ${textColorVar};
        font-size: ${contentFontSizeVar};

        margin-top: ${marginTop};
        margin-bottom: ${marginBottom};
        margin-left: ${marginLeft};
        padding-top: 10px;
        padding-bottom: 10px;
        padding-left: ${paddingLeft};
        padding-right: 10px;

        border-radius: 5px;
        box-shadow: 0 1px 3px rgba(0,0,0,0.1);

        width: calc(100% - ${marginLeft});
        max-width: calc(100% - ${marginLeft});
        overflow-x: hidden;
    `;

            // Removed the side rectangle logic that was here:
            // if (isTopLevelMessage && threadColor) { ... }

            const messageHeader = document.createElement('div');

            messageHeader.style.cssText = `
                font-size: 12px;
                color: ${headerTextColorVar};
                font-weight: bold;
                margin-bottom: 8px;
                padding-bottom: 5px;
                border-bottom: 1px solid ${headerBorderVar};
                display: flex;
                align-items: center;
                width: 100%;
            `;


            if (shouldDisableUnderline) {
                messageHeader.style.borderBottom = 'none';
                messageHeader.style.paddingBottom = '0px';
                messageHeader.style.marginBottom = '8px'; // Keep consistent margin even when underline is hidden
                messageHeader.style.lineHeight = '1.1';   // Standardized
                messageHeader.style.minHeight = '0';      // Standardized
            }

            const timestampParts = formatTimestampForHeader(message.time);

            if (isTopLevelMessage) {
                messageHeader.style.justifyContent = 'space-between'; // For ID+Time (left) and Date (right)

                // Create a container for the color square and the ID/Time text
                const leftHeaderContent = document.createElement('span');
                leftHeaderContent.style.display = 'flex'; // Use flex to align square and text
                leftHeaderContent.style.alignItems = 'center'; // Vertically align items in the flex container

                if (threadColor) {
                    const colorSquare = document.createElement('span');
                    colorSquare.style.cssText = `
                        display: inline-block;
                        width: 10px; /* Adjust size as needed */
                        height: 10px; /* Adjust size as needed */
                        background-color: ${threadColor};
                        margin-right: 6px; /* Space between square and '#' */
                        border-radius: 2px; /* Optional: for rounded corners */
                        flex-shrink: 0; /* Prevent square from shrinking */
                        border: var(--otk-viewer-thread-box-outline, none);
                    `;
                    leftHeaderContent.appendChild(colorSquare);
                }

                const idSpan = document.createElement('span');
                idSpan.textContent = `#${message.id}`;
                idSpan.style.cursor = 'pointer';
                if (isFiltered) {
                    idSpan.style.textDecoration = 'line-through';
                }
                idSpan.addEventListener('click', (e) => {
                    e.stopPropagation();
                    const threadUrl = `https://boards.4chan.org/b/thread/${message.originalThreadId}`;
                    const popup = window.open(threadUrl, '_blank', 'width=460,height=425,resizable,scrollbars');
                    if (popup) {
                        popup.addEventListener('load', () => {
                            const script = popup.document.createElement('script');
                            script.textContent = `
                                const messageId = "${message.id}";
                                const selector = \`#pi\${messageId} > span.postNum.desktop > a:nth-child(2)\`;
                                const link = document.querySelector(selector);
                                if (link) {
                                    link.click();
                                }
                            `;
                            popup.document.body.appendChild(script);
                        }, true);
                    }
                });

                const timeTextSpan = document.createElement('span');
                timeTextSpan.textContent = `\u00A0| ${timestampParts.time}`;
                if (isFiltered) {
                    timeTextSpan.style.textDecoration = 'line-through';
                }
                leftHeaderContent.appendChild(idSpan);

                leftHeaderContent.appendChild(timeTextSpan);

                const blockIcon = document.createElement('span');
                blockIcon.innerHTML = '&#128711;'; // Block icon
                blockIcon.style.cssText = 'margin-left: 10px; cursor: pointer;';

                if (isFiltered) {
                    blockIcon.style.color = 'red';
                    blockIcon.title = 'This message is blocked by your filters.';
                } else {
                    blockIcon.style.visibility = 'hidden';
                    blockIcon.title = 'Create filter for this message';
                leftHeaderContent.addEventListener('mouseenter', () => {
                        blockIcon.style.visibility = 'visible';
                    });
                leftHeaderContent.addEventListener('mouseleave', () => {
                        blockIcon.style.visibility = 'hidden';
                    });
                }
                leftHeaderContent.appendChild(blockIcon);

                blockIcon.addEventListener('click', (e) => {
                    e.stopPropagation();

                    const hasText = message.text && message.text.replace(/>>\d+(\s\(You\))?/g, '').trim().length > 0;
                    const hasAttachment = message.attachment && message.attachment.filehash_db_key;

                    const newRule = {
                        id: Date.now(),
                        action: 'filterOut',
                        enabled: true,
                        category: 'keyword', // default
                        matchContent: '',
                        replaceContent: ''
                    };

                    if (hasText && hasAttachment) {
                        newRule.category = 'entireMessage';
                        try {
                            newRule.matchContent = JSON.stringify({
                                text: message.text.replace(/>>\d+(\s\(You\))?/g, '').trim(),
                                media: `md5:${message.attachment.filehash_db_key}`
                            }, null, 2);
                        } catch (err) {
                            consoleError("Failed to stringify composite filter", err);
                            // Fallback to simpler filter if stringify fails
                            newRule.category = 'attachedMedia';
                            newRule.matchContent = `md5:${message.attachment.filehash_db_key}`;
                        }
                    } else if (hasText) {
                        newRule.category = 'keyword';
                        newRule.matchContent = message.text.replace(/>>\d+(\s\(You\))?/g, '').trim();
                    } else if (hasAttachment) {
                        newRule.category = 'attachedMedia';
                        newRule.matchContent = `md5:${message.attachment.filehash_db_key}`;
                    }

                    const filterWindow = document.getElementById('otk-filter-window');
                    if (filterWindow) {
                        filterWindow.style.display = 'flex';
                        renderFilterEditorView(newRule);
                    }
                });

                const dateSpan = document.createElement('span');
                dateSpan.textContent = timestampParts.date;
                if (isFiltered) {
                    dateSpan.style.textDecoration = 'line-through';
                }

                const rightHeaderContent = document.createElement('span');
                rightHeaderContent.style.display = 'flex';
                rightHeaderContent.style.alignItems = 'center';

                if (hasTruncatedQuotes(message)) { // Use the recursive check for initial display
                    const plusIcon = document.createElement('span');
                    plusIcon.classList.add('otk-plus-icon');
                    plusIcon.id = `otk-plus-icon-${message.id}`;
                    plusIcon.textContent = '+';
                    plusIcon.style.color = '#000000';
                    plusIcon.title = 'Load next reply in truncated chain';
                    plusIcon.style.fontWeight = 'bold';
                    plusIcon.style.fontSize = '18px';
                    plusIcon.style.lineHeight = '24px';
                    plusIcon.style.marginRight = '8px';
                    plusIcon.style.cursor = 'pointer';
                    plusIcon.style.width = '24px';
                    plusIcon.style.height = '24px';
                    plusIcon.style.display = 'flex';
                    plusIcon.style.alignItems = 'center';
                    plusIcon.style.justifyContent = 'center';
                    plusIcon.style.borderRadius = '4px';
                    plusIcon.style.backgroundColor = 'var(--otk-plus-icon-bg-color)';

                    plusIcon.addEventListener('click', async (e) => {
                        e.stopPropagation();

                        const clickedPlusIcon = e.currentTarget;
                        const topLevelElement = clickedPlusIcon.closest('.otk-message-container-main');
                        if (!topLevelElement) {
                            consoleError("Could not find top-level container for the clicked plus icon.");
                            return;
                        }

                        const truncatedInfo = findNextUnloadedQuoteLink(topLevelElement);

                        if (!truncatedInfo) {
                            consoleWarn(`Plus icon clicked for message ${message.id}, but no further truncated quotes could be found. Removing icon.`);
                            clickedPlusIcon.remove();
                            return;
                        }

                        const { id: messageToLoadId, parentId: parentOfTruncatedId } = truncatedInfo;

                        let messageToLoad = findMessageById(messageToLoadId);
                        if (!messageToLoad) {
                            clickedPlusIcon.style.cursor = 'wait';
                            clickedPlusIcon.style.color = '#aaa';
                            try {
                                await fetchThreadMessages(message.originalThreadId);
                                messageToLoad = findMessageById(messageToLoadId);
                            } catch (error) {
                                consoleError(`Failed to fetch thread for click-to-load:`, error);
                                return;
                            } finally {
                                clickedPlusIcon.style.cursor = 'pointer';
                                clickedPlusIcon.style.color = threadColor;
                            }
                        }

                        if (!messageToLoad) {
                            consoleError(`Message ${messageToLoadId} not found even after fetching thread.`);
                            return;
                        }

                        const insertionParent = topLevelElement.querySelector(`div[data-message-id='${parentOfTruncatedId}']`);
                        if (!insertionParent) {
                            consoleError(`Could not find insertion parent element with ID ${parentOfTruncatedId}`);
                            return;
                        }

                        // We need the actual depth of the parent to correctly render the new child's own quotes.
                        const parentMessageObject = findMessageById(parentOfTruncatedId);
                        const parentActualDepth = findMessageDepth(message, parentOfTruncatedId);


                        const parentVisualDepth = insertionParent.dataset.visualDepth;
                        const newVisualDepth = (parentVisualDepth === undefined) ? 1 : parseInt(parentVisualDepth, 10) + 1;

                        const newElement = createMessageElementDOM(
                            messageToLoad, [], uniqueImageViewerHashes,
                            messageToLoad.board || 'b', false, (parentActualDepth !== null ? parentActualDepth + 1 : 0),
                            null, parentOfTruncatedId, new Set(), newVisualDepth
                        );

                        if (newElement) {
                            insertionParent.appendChild(newElement);

                            // Re-check if there are any more unloaded truncated quotes using the same DOM-based logic.
                            const nextTruncatedInfo = findNextUnloadedQuoteLink(topLevelElement);
                            if (!nextTruncatedInfo) {
                                clickedPlusIcon.remove();
                            }
                        }
                    });

                    rightHeaderContent.appendChild(plusIcon);
                }

                rightHeaderContent.appendChild(dateSpan);

                messageHeader.appendChild(leftHeaderContent);
                messageHeader.appendChild(rightHeaderContent);
            } else { // Simplified header for quoted messages
                messageHeader.style.justifyContent = 'flex-start'; // Align ID to the start

                const headerContentWrapper = document.createElement('span');
                headerContentWrapper.style.display = 'flex';
                headerContentWrapper.style.alignItems = 'center';

                const idSpan = document.createElement('span');
                idSpan.textContent = ` >>${message.id}`; // Changed prefix for quoted messages
                idSpan.style.cursor = 'pointer';
                if (isFiltered) {
                    idSpan.style.textDecoration = 'line-through';
                }
                idSpan.addEventListener('click', (e) => {
                    e.stopPropagation();
                    const threadUrl = `https://boards.4chan.org/b/thread/${message.originalThreadId}`;
                    const popup = window.open(threadUrl, '_blank', 'width=460,height=425,resizable,scrollbars,popup=true');
                    if (popup) {
                        popup.addEventListener('load', () => {
                            const script = popup.document.createElement('script');
                            script.textContent = `
                                const messageId = "${message.id}";
                                const selector = \`#pi\${messageId} > span.postNum.desktop > a:nth-child(2)\`;
                                const link = document.querySelector(selector);
                                if (link) {
                                    link.click();
                                }
                            `;
                            popup.document.body.appendChild(script);
                        }, true);
                    }
                });
                headerContentWrapper.appendChild(idSpan);

                const blockIcon = document.createElement('span');
                blockIcon.innerHTML = '&#128711;'; // Block icon
                blockIcon.style.cssText = 'margin-left: 10px; cursor: pointer;';

                if (isFiltered) {
                    blockIcon.style.color = 'red';
                    blockIcon.title = 'This message is blocked by your filters.';
                } else {
                    blockIcon.style.visibility = 'hidden';
                    blockIcon.title = 'Create filter for this message';
                    headerContentWrapper.addEventListener('mouseenter', () => {
                        blockIcon.style.visibility = 'visible';
                    });
                    headerContentWrapper.addEventListener('mouseleave', () => {
                        blockIcon.style.visibility = 'hidden';
                    });
                }
                headerContentWrapper.appendChild(blockIcon);
                messageHeader.appendChild(headerContentWrapper);

                blockIcon.addEventListener('click', (e) => {
                    e.stopPropagation();

                    const hasText = message.text && message.text.replace(/>>\d+(\s\(You\))?/g, '').trim().length > 0;
                    const hasAttachment = message.attachment && message.attachment.filehash_db_key;

                    const newRule = {
                        id: Date.now(),
                        action: 'filterOut',
                        enabled: true,
                        category: 'keyword', // default
                        matchContent: '',
                        replaceContent: ''
                    };

                    if (hasText && hasAttachment) {
                        newRule.category = 'entireMessage';
                         try {
                            newRule.matchContent = JSON.stringify({
                                text: message.text.replace(/>>\d+(\s\(You\))?/g, '').trim(),
                                media: `md5:${message.attachment.filehash_db_key}`
                            }, null, 2);
                        } catch (err) {
                            consoleError("Failed to stringify composite filter", err);
                            // Fallback to simpler filter if stringify fails
                            newRule.category = 'attachedMedia';
                            newRule.matchContent = `md5:${message.attachment.filehash_db_key}`;
                        }
                    } else if (hasText) {
                        newRule.category = 'keyword';
                        newRule.matchContent = message.text.replace(/>>\d+(\s\(You\))?/g, '').trim();
                    } else if (hasAttachment) {
                        newRule.category = 'attachedMedia';
                        newRule.matchContent = `md5:${message.attachment.filehash_db_key}`;
                    }

                    const filterWindow = document.getElementById('otk-filter-window');
                    if (filterWindow) {
                        filterWindow.style.display = 'flex';
                        renderFilterEditorView(newRule);
                    }
                });
            }
            messageDiv.appendChild(messageHeader);
            const [textElement, attachmentDiv] = _populateMessageBody(processedMessage, mediaLoadPromises, uniqueImageViewerHashes, boardForLink, isTopLevelMessage, currentDepth, threadColor, parentMessageId, newAncestors, allThemeSettings, shouldDisplayFilenames, shouldDisableUnderline);

            // Click listener for anchoring
            const persistentInstanceId = `otk-msg-${parentMessageId || 'toplevel'}-${message.id}`;
            messageDiv.id = persistentInstanceId;
            messageDiv.setAttribute('data-original-message-id', message.id);

            messageDiv.addEventListener('click', (event) => {
                const target = event.target;
                let preventAnchor = false;

                // Standard interactive elements that should not trigger anchoring
                if (target.matches('a, img, video, iframe, input, button, select, textarea') ||
                    target.closest('a, img, video, iframe, input, button, select, textarea') ||
                    target.isContentEditable) {
                    preventAnchor = true;
                }

                // Specific wrapper classes for embeds that should not trigger anchoring
                if (!preventAnchor) {
                    const specificWrappers = [
                        '.thumbnail-link',
                        '.otk-youtube-embed-wrapper',
                        '.otk-twitch-embed-wrapper',
                        '.otk-streamable-embed-wrapper'
                    ];
                    if (specificWrappers.some(cls => target.matches(cls) || target.closest(cls))) {
                        preventAnchor = true;
                    }
                }

                if (preventAnchor) {
                    return; // Do not anchor
                }

                if (!isTopLevelMessage) {
                    event.stopPropagation();
                }

                const isThisMessageAlreadyAnchored = messageDiv.classList.contains(ANCHORED_MESSAGE_CLASS);

                // Un-highlight all currently anchored messages
                document.querySelectorAll(`.${ANCHORED_MESSAGE_CLASS}`).forEach(el => {
                    el.classList.remove(ANCHORED_MESSAGE_CLASS);
                });

                if (isThisMessageAlreadyAnchored) {
                    // If the clicked message was the anchor, un-anchor it
                    localStorage.removeItem(ANCHORED_MESSAGE_ID_KEY);
                    consoleLog(`Un-anchored message instance: ${persistentInstanceId}`);
                } else {
                    // Otherwise, anchor this new message
                    messageDiv.classList.add(ANCHORED_MESSAGE_CLASS);
                    localStorage.setItem(ANCHORED_MESSAGE_ID_KEY, persistentInstanceId);
                    consoleLog(`Anchored new message instance: ${persistentInstanceId}`);
                }
            });

            // Initial highlight check when the element is first created
            const initiallyStoredAnchoredId = localStorage.getItem(ANCHORED_MESSAGE_ID_KEY);
            consoleLog("initiallyStoredAnchoredId", initiallyStoredAnchoredId, "persistentInstanceId", persistentInstanceId);
            if (persistentInstanceId === initiallyStoredAnchoredId) {
                messageDiv.classList.add(ANCHORED_MESSAGE_CLASS);
            }

            if (isFiltered) {
                const hasQuotes = textElement.querySelector('div[data-message-id]') !== null;
                const hasUnfilteredContent = ((processedMessage.text || '').trim().length > 0) || (processedMessage.attachment !== null);

                if (!hasUnfilteredContent && !hasQuotes) {
                    // Case 1: No unfiltered content and no quotes. Collapse the original message.
                    const [originalTextElement, originalAttachmentDiv] = _populateMessageBody(message, mediaLoadPromises, uniqueImageViewerHashes, boardForLink, isTopLevelMessage, currentDepth, threadColor, parentMessageId, newAncestors, allThemeSettings, shouldDisplayFilenames, shouldDisableUnderline);
                    const collapsibleContainer = wrapInCollapsibleContainer([originalTextElement, originalAttachmentDiv]);
                    messageDiv.appendChild(collapsibleContainer);
                } else {
                    // Case 2: Has unfiltered content or quotes. Show processed content with an eye icon to toggle original.
                    const blockIcon = messageHeader.querySelector('span[title*="blocked"]');
                    if (blockIcon) {
                        const eyeIcon = document.createElement('span');
                        eyeIcon.innerHTML = '👁️';
                        eyeIcon.style.cssText = 'margin-left: 5px; cursor: pointer;';
                        eyeIcon.title = 'Show filtered content';
                        blockIcon.parentNode.insertBefore(eyeIcon, blockIcon.nextSibling);

                        const bodyContainer = document.createElement('div');
                        const processedBodyContainer = document.createElement('div');
                        processedBodyContainer.append(textElement);
                        if (attachmentDiv) {
                            processedBodyContainer.append(attachmentDiv);
                        }

                        const originalBodyContainer = document.createElement('div');
                        originalBodyContainer.style.display = 'none';

                        bodyContainer.appendChild(processedBodyContainer);
                        bodyContainer.appendChild(originalBodyContainer);
                        messageDiv.appendChild(bodyContainer);

                        let originalBodyGenerated = false;

                        eyeIcon.addEventListener('click', (e) => {
                            e.stopPropagation();
                            if (!originalBodyGenerated) {
                                const [originalTextElement, originalAttachmentDiv] = _populateMessageBody(message, mediaLoadPromises, uniqueImageViewerHashes, boardForLink, isTopLevelMessage, currentDepth, threadColor, parentMessageId, newAncestors, allThemeSettings, shouldDisplayFilenames, shouldDisableUnderline);
                                if(originalTextElement) originalBodyContainer.append(originalTextElement);
                                if (originalAttachmentDiv) originalBodyContainer.append(originalAttachmentDiv);
                                originalBodyGenerated = true;
                            }

                            const isProcessedVisible = processedBodyContainer.style.display !== 'none';
                            processedBodyContainer.style.display = isProcessedVisible ? 'none' : 'block';
                            originalBodyContainer.style.display = isProcessedVisible ? 'block' : 'none';
                            eyeIcon.title = isProcessedVisible ? 'Hide filtered content' : 'Show filtered content';
                        });
                    } else {
                        // Fallback if block icon isn't found for some reason
                        messageDiv.appendChild(textElement);
                        if (attachmentDiv) {
                            messageDiv.appendChild(attachmentDiv);
                        }
                    }
                }
            } else {
                // Original logic for non-filtered messages
                messageDiv.appendChild(textElement);
                if (attachmentDiv) {
                    messageDiv.appendChild(attachmentDiv);
                }
            }
            return messageDiv;
        } // End of else (default layout)
    }



    function createThumbnailElement(attachment, board) {
        const thumbLink = document.createElement('a');
        thumbLink.href = `https://i.4cdn.org/${board}/${attachment.tim}${attachment.ext}`;
        thumbLink.target = '_blank';

        const thumbImg = document.createElement('img');
        thumbImg.src = `https://i.4cdn.org/${board}/${attachment.tim}s.jpg`; // Standard thumbnail URL format
        thumbImg.alt = attachment.filename;
        thumbImg.style.maxWidth = `${attachment.tn_w}px`;
        thumbImg.style.maxHeight = `${attachment.tn_h}px`;
        thumbImg.style.border = '1px solid #555';
        thumbImg.style.borderRadius = '3px';

        thumbLink.appendChild(thumbImg);
        return thumbLink;
    }

    async function scanCatalog() {
        const url = 'https://a.4cdn.org/b/catalog.json';
        try {
            const response = await fetch(url, { cache: 'no-store' }); // Avoid browser caching catalog
            if (!response.ok) throw new Error(`Catalog fetch failed: ${response.status} ${response.statusText}`);
            const catalog = await response.json();

            let foundThreads = [];
            const keywordsString = localStorage.getItem(OTK_TRACKED_KEYWORDS_KEY) || "otk";
            const keywords = keywordsString.split(',')
                .map(k => k.trim().toLowerCase())
                .filter(k => k.length > 0);

            if (keywords.length === 0) { // Should not happen if default is "otk" but as a safeguard
                consoleWarn("scanCatalog: No valid keywords configured. Defaulting to 'otk'.");
                keywords.push("otk");
            }
            consoleLog(`scanCatalog: Using keywords for search: [${keywords.join(', ')}]`);

            catalog.forEach(page => {
                page.threads.forEach(thread => {
                    const title = (thread.sub || '').toLowerCase();
                    // const com = (thread.com || '').toLowerCase(); // No longer needed
                    // const combinedText = title + " " + com; // No longer needed

                    if (keywords.some(keyword => title.includes(keyword)) && !blockedThreads.has(Number(thread.no))) {
                        foundThreads.push({
                            id: Number(thread.no),
                            title: thread.sub || `Thread ${thread.no}` // Store original case title
                        });
                    }
                });
            });
            consoleLog(`scanCatalog: Found ${foundThreads.length} threads matching keywords:`, foundThreads.map(t => t.id));
            return foundThreads;
        } catch (error) {
            consoleError('scanCatalog error:', error);
            return [];
        }
    }

    async function fetchThreadMessages(threadId) {
        // consoleLog('[DebugRefreshV2-FTM] START for threadId:', threadId); // Removed
        const url = `https://a.4cdn.org/b/thread/${threadId}.json`;
        const headers = {}; // Initialize empty headers object
        const metadata = threadFetchMetadata[threadId];

        if (metadata) {
            // consoleLog('[DebugRefreshV2-FTM] Preparing headers for threadId:', threadId, 'Current metadata:', JSON.stringify(metadata)); // Removed
            if (metadata.etag) {
                headers['If-None-Match'] = metadata.etag;
                // consoleLog('[DebugRefreshV2-FTM] Sending If-None-Match for', threadId, ':', headers['If-None-Match']); // Removed
            } else if (metadata.lastModified) {
                headers['If-Modified-Since'] = metadata.lastModified;
                // consoleLog('[DebugRefreshV2-FTM] Sending If-Modified-Since for', threadId, ':', headers['If-Modified-Since']); // Removed
            }
        } else {
            // consoleLog('[DebugRefreshV2-FTM] No metadata found for threadId:', threadId, 'Performing full fetch.'); // Removed
        }

        let response;
        try {
            response = await fetch(url, { headers: headers });
            // consoleLog('[DebugRefreshV2-FTM] Response status for', threadId, ':', response.status, 'OK:', response.ok); // Removed

            if (response.status === 304) {
                consoleLog(`Thread ${threadId} not modified (304).`);
                return { status: 'not_modified', threadId: threadId, messages: [], counts: { fetchedMessages: 0, fetchedImages: 0, fetchedVideos: 0, newlyStoredImages: 0, newlyStoredVideos: 0 } };
            }

            const defaultEmptyReturn = { messages: [], counts: { fetchedMessages: 0, fetchedImages: 0, fetchedVideos: 0, newlyStoredImages: 0, newlyStoredVideos: 0 } };

            if (!response.ok) { // Handles non-304 errors
                consoleWarn(`Fetch error for thread ${threadId}: ${response.status} ${response.statusText}`);
                if (response.status === 404) {
                    delete threadFetchMetadata[threadId]; // Clear metadata on 404
                }
                return defaultEmptyReturn; // Return new structure on error
            }

            // If response is OK (200), store new ETag/Last-Modified
            const newEtag = response.headers.get('ETag');
            const newLastModified = response.headers.get('Last-Modified');

            if (newEtag || newLastModified) {
                threadFetchMetadata[threadId] = {}; // Initialize/clear existing for this thread
                if (newEtag) {
                    threadFetchMetadata[threadId].etag = newEtag;
                }
                if (newLastModified) {
                    threadFetchMetadata[threadId].lastModified = newLastModified;
                }
                // consoleLog('[DebugRefreshV2-FTM] Stored new metadata for threadId:', threadId, 'New metadata:', JSON.stringify(threadFetchMetadata[threadId])); // Removed
                consoleLog(`Stored new ETag/Last-Modified for thread ${threadId}.`); // Standard log
            } else {
                // consoleLog('[DebugRefreshV2-FTM] No new ETag/Last-Modified headers found on 200 OK for threadId:', threadId); // Removed
                if (metadata) { // Only clear if old metadata existed and server stopped sending new ones
                    // consoleLog('[DebugRefreshV2-FTM] Clearing old metadata for threadId:', threadId, 'as no new headers were provided.'); // Removed
                    consoleLog(`No new ETag/Last-Modified for thread ${threadId}, clearing old metadata.`); // Standard log
                    delete threadFetchMetadata[threadId];
                }
            }

            const threadData = await response.json();
            // consoleLog('[DebugRefreshV2-FTM] Successfully got JSON for threadId:', threadId, 'Post count in JSON:', threadData.posts ? threadData.posts.length : 'N/A'); // Removed
            if (!threadData.posts || threadData.posts.length === 0) {
                consoleLog(`No posts in JSON for thread ${threadId}.`);
                return defaultEmptyReturn; // Return new structure if no posts
            }

            const opPost = threadData.posts[0];
            const posts = threadData.posts;
            const processedMessages = [];
            let fetchedMessagesInThread = 0;
            let fetchedImagesInThread = 0;
            let fetchedVideosInThread = 0;
            let newlyStoredImagesInThread = 0;
            let newlyStoredVideosInThread = 0;

            for (const post of posts) {
                fetchedMessagesInThread++;
                const message = {
                    id: post.no,
                    time: post.time,
                    originalThreadId: threadId, // Store the original thread ID for color lookup
                    text: '', // Will be populated after decoding
                    title: opPost.sub ? toTitleCase(decodeEntities(opPost.sub)) : `Thread ${threadId}`, // Assuming decodeEntities here handles what it needs for title
                    attachment: null
                };

                if (post.com) {
                    let rawText = post.com.replace(/<br\s*\/?>/gi, '\n').replace(/<[^>]+>/g, '');
                    // Specific log for problematic strings if they occur
                    if (rawText.includes('&#039;') || rawText.includes('&amp;#039;')) {
                        consoleLog(`[Entity Debug] Original post.com for post ${post.no}:`, post.com);
                        consoleLog(`[Entity Debug] Text after tag strip for post ${post.no}:`, rawText);
                    }
                    message.text = decodeAllHtmlEntities(rawText);
                    if (rawText.includes('&#039;') || rawText.includes('&amp;#039;')) {
                        consoleLog(`[Entity Debug] Text after decodeAllHtmlEntities for post ${post.no}:`, message.text);
                    }
                } else {
                    message.text = '';
                }

                if (post.filename && post.tim && post.ext) {
                    let filehash_db_key;
                    const postMd5 = post.md5 ? post.md5.trim() : null;

                    if (postMd5 && postMd5.length > 0 && postMd5 !== "                                        ") { // Check for valid MD5
                        filehash_db_key = postMd5;
                    } else {
                        filehash_db_key = `${post.tim}${post.ext}`;
                        consoleWarn(`MD5 hash not available or invalid for post ${post.no}, file ${post.filename}. Falling back to tim+ext for DB key: ${filehash_db_key}`);
                    }

                    message.attachment = {
                        filename: post.filename,
                        ext: post.ext,
                        tn_w: post.tn_w,
                        tn_h: post.tn_h,
                        tim: post.tim, // Keep original tim for reference / thumbnail URL
                        w: post.w,
                        h: post.h,
                        fsize: post.fsize,
                        md5: post.md5, // Original MD5 from API
                        filehash_db_key: filehash_db_key, // The key used for IndexedDB
                        localStoreId: null, // Will be set to filehash_db_key if stored
                        tn_w: post.tn_w,
                        tn_h: post.tn_h
                    };

                    // Check if media is already in IndexedDB
                    if (otkMediaDB) {
                        try {
                            const transaction = otkMediaDB.transaction(['mediaStore'], 'readonly');
                            const store = transaction.objectStore('mediaStore');
                            const dbRequest = store.get(filehash_db_key);

                            const dbResult = await new Promise((resolve, reject) => {
                                dbRequest.onsuccess = () => resolve(dbRequest.result);
                                dbRequest.onerror = (dbEvent) => {
                                    consoleError(`IndexedDB 'get' error for key ${filehash_db_key} (post ${post.no}):`, dbEvent.target.error);
                                    reject(dbEvent.target.error);
                                };
                            });

                            if (dbResult) {
                                consoleLog(`Media with key ${filehash_db_key} (post ${post.no}) already in IndexedDB.`);
                                message.attachment.localStoreId = filehash_db_key;
                            } else {
                                // Not in DB, try to download and store
                                const mediaUrl = `https://i.4cdn.org/${opPost.board || 'b'}/${post.tim}${post.ext}`;
                                consoleLog(`Downloading media for post ${post.no} (DB key: ${filehash_db_key}) from ${mediaUrl}`);
                                try {
                                    const mediaResponse = await new Promise((resolve, reject) => {
                                        GM_xmlhttpRequest({
                                            method: "GET",
                                            url: mediaUrl,
                                            responseType: 'blob',
                                            onload: (response) => {
                                                if (response.status === 200) {
                                                    resolve(response.response);
                                                } else {
                                                    reject(new Error(`Failed to fetch media: ${response.status}`));
                                                }
                                            },
                                            onerror: (error) => {
                                                reject(error);
                                            }
                                        });
                                    });

                                    if (mediaResponse) {
                                        const blob = mediaResponse;
                                        const storeTransaction = otkMediaDB.transaction(['mediaStore'], 'readwrite');
                                        const mediaStore = storeTransaction.objectStore('mediaStore');

                                        // Stored object's key property must match the store's keyPath ('filehash')
                                        const itemToStore = {
                                            filehash: filehash_db_key, // This is the keyPath value
                                            blob: blob,
                                            originalThreadId: threadId,
                                            filename: post.filename,
                                            ext: post.ext, // Store ext for easier type identification for stats
                                            timestamp: Date.now(),
                                            isThumbnail: false // Mark that this is not a thumbnail
                                        };

                                        const putRequest = mediaStore.put(itemToStore);
                                        await new Promise((resolvePut, rejectPut) => {
                                            putRequest.onsuccess = () => {
                                                message.attachment.localStoreId = filehash_db_key;
                                                consoleLog(`Stored full media with key ${filehash_db_key} (post ${post.no}) in IndexedDB.`);

                                                const extLower = post.ext.toLowerCase();
                                                if (['.jpg', '.jpeg', '.png', '.gif'].includes(extLower)) {
                                                    newlyStoredImagesInThread++;
                                                    let currentImageCount = parseInt(localStorage.getItem(LOCAL_IMAGE_COUNT_KEY) || '0');
                                                    localStorage.setItem(LOCAL_IMAGE_COUNT_KEY, (currentImageCount + 1).toString());
                                                } else if (['.webm', '.mp4'].includes(extLower)) {
                                                    newlyStoredVideosInThread++;
                                                    let currentVideoCount = parseInt(localStorage.getItem(LOCAL_VIDEO_COUNT_KEY) || '0');
                                                    localStorage.setItem(LOCAL_VIDEO_COUNT_KEY, (currentVideoCount + 1).toString());
                                                }
                                                updateDisplayedStatistics();
                                                resolvePut();
                                            };
                                            putRequest.onerror = (putEvent) => {
                                                consoleError(`IndexedDB 'put' error for full media key ${filehash_db_key} (post ${post.no}):`, putEvent.target.error);
                                                rejectPut(putEvent.target.error);
                                            };
                                        });
                                    } else {
                                        consoleWarn(`Failed to download full media for post ${post.no} (DB key: ${filehash_db_key}). Status: ${mediaResponse.status}`);
                                    }
                                } catch (fetchError) {
                                    consoleError(`Network error when fetching media for post ${post.no} (DB key: ${filehash_db_key}):`, fetchError);
                                }
                            }

                            // --- Thumbnail Fetching and Storing (if image) ---
                            const extLower = post.ext.toLowerCase();
                            if (['.jpg', '.jpeg', '.png', '.gif'].includes(extLower)) { // Only try to fetch thumbs for image types
                                const thumbnail_filehash_db_key = filehash_db_key + '_thumb';
                                message.attachment.localThumbStoreId = null; // Initialize

                                // Create a new transaction specifically for getting the thumbnail
                                const thumbGetTransaction = otkMediaDB.transaction(['mediaStore'], 'readonly');
                                const thumbGetStore = thumbGetTransaction.objectStore('mediaStore');
                                const thumbDbRequest = thumbGetStore.get(thumbnail_filehash_db_key);

                                const thumbDbResult = await new Promise((resolve, reject) => {
                                    thumbDbRequest.onsuccess = () => resolve(thumbDbRequest.result);
                                    // thumbGetTransaction will complete after this promise resolves or rejects
                                    thumbGetTransaction.oncomplete = () => consoleLog(`Thumb get transaction completed for ${thumbnail_filehash_db_key}`);
                                    thumbGetTransaction.onerror = (event) => consoleError(`Thumb get transaction error for ${thumbnail_filehash_db_key}:`, event.target.error);

                                    thumbDbRequest.onerror = (dbEvent) => {
                                        consoleError(`IndexedDB 'get' error for thumbnail key ${thumbnail_filehash_db_key} (post ${post.no}):`, dbEvent.target.error);
                                        reject(dbEvent.target.error);
                                    };
                                });

                                if (thumbDbResult) {
                                    consoleLog(`Thumbnail with key ${thumbnail_filehash_db_key} (post ${post.no}) already in IndexedDB.`);
                                    message.attachment.localThumbStoreId = thumbnail_filehash_db_key;
                                } else {
                                    const thumbUrl = `https://i.4cdn.org/${opPost.board || 'b'}/${post.tim}s.jpg`;
                                    consoleLog(`Downloading thumbnail for post ${post.no} (DB key: ${thumbnail_filehash_db_key}) from ${thumbUrl}`);
                                    try {
                                        const thumbResponse = await new Promise((resolve, reject) => {
                                            GM_xmlhttpRequest({
                                                method: "GET",
                                                url: thumbUrl,
                                                responseType: 'blob',
                                                onload: (response) => {
                                                    if (response.status === 200) {
                                                        resolve(response.response);
                                                    } else {
                                                        reject(new Error(`Failed to fetch thumbnail: ${response.status}`));
                                                    }
                                                },
                                                onerror: (error) => {
                                                    reject(error);
                                                }
                                            });
                                        });
                                        if (thumbResponse) {
                                            const thumbBlob = thumbResponse;
                                            const thumbStoreTransaction = otkMediaDB.transaction(['mediaStore'], 'readwrite'); // New transaction
                                            const thumbMediaStore = thumbStoreTransaction.objectStore('mediaStore');
                                            const thumbItemToStore = {
                                                filehash: thumbnail_filehash_db_key,
                                                blob: thumbBlob,
                                                originalThreadId: threadId,
                                                filename: `${post.filename}_thumb.jpg`, // Adjust filename
                                                ext: '.jpg', // Thumbnails are typically jpg
                                                timestamp: Date.now(),
                                                isThumbnail: true // Mark that this IS a thumbnail
                                            };
                                            const thumbPutRequest = thumbMediaStore.put(thumbItemToStore);
                                            await new Promise((resolvePut, rejectPut) => {
                                                thumbPutRequest.onsuccess = () => {
                                                    message.attachment.localThumbStoreId = thumbnail_filehash_db_key;
                                                    consoleLog(`Stored thumbnail with key ${thumbnail_filehash_db_key} (post ${post.no}) in IndexedDB.`);
                                                    // Do NOT increment LOCAL_IMAGE_COUNT_KEY or newlyStoredImagesInThread for thumbnails here
                                                    // to avoid double counting if the main image is also counted.
                                                    resolvePut();
                                                };
                                                thumbPutRequest.onerror = (putEvent) => {
                                                    consoleError(`IndexedDB 'put' error for thumbnail key ${thumbnail_filehash_db_key} (post ${post.no}):`, putEvent.target.error);
                                                    rejectPut(putEvent.target.error);
                                                };
                                            });
                                        } else {
                                            consoleWarn(`Failed to download thumbnail for post ${post.no} (DB key: ${thumbnail_filehash_db_key}). Status: ${thumbResponse.status}`);
                                        }
                                    } catch (thumbFetchError) {
                                        consoleError(`Error fetching thumbnail for post ${post.no} (DB key: ${thumbnail_filehash_db_key}):`, thumbFetchError);
                                    }
                                }
                            }
                            // --- End Thumbnail Fetching ---

                        } catch (dbError) {
                            consoleError(`General IndexedDB error for post ${post.no} (DB key: ${filehash_db_key}):`, dbError);
                        }
                    } else {
                        consoleWarn('otkMediaDB not available for media operations (post ${post.no}).');
                    }
                }
                // If attachment was not stored (e.g., already in DB or download failed), but is an image/video, still count as fetched.
                // This logic is slightly complex because the primary counting for fetchedImages/Videos happens inside the IDB storage path.
                // A simpler way for fetched media is to count them when `message.attachment` is first processed.
                if (post.filename && post.ext) { // This block is outside the IDB check, runs if attachment exists
                    const ext = post.ext.toLowerCase();
                    if (['.jpg', '.jpeg', '.png', '.gif'].includes(ext)) {
                        // If not already counted by the IDB storage success path (e.g. it was already in DB or failed download)
                        // This can lead to double counting if not careful.
                        // Let's refine: `fetchedImagesInThread` should be incremented once when an image attachment is identified.
                        // The current location increments it only on successful *new* store.
                        // This will be handled by moving the increment outside the successful store block or before it.
                        // For now, the current logic for `newlyStoredImagesInThread` is correct.
                        // `fetchedImagesInThread` needs to be incremented unconditionally if `post.ext` is an image type.
                    } else if (['.webm', '.mp4'].includes(ext)) {
                        // Similar for videos.
                    }
                }
                processedMessages.push(message);
            }

            // Refined counting for fetched media (regardless of storage status)
            // This ensures fetchedImagesInThread and fetchedVideosInThread are accurate even if media was already in DB.
            // The newlyStoredImagesInThread is correctly counted only upon successful new storage.
            let trueFetchedImages = 0;
            let trueFetchedVideos = 0;
            processedMessages.forEach(msg => {
                if (msg.attachment && msg.attachment.ext) {
                    const ext = msg.attachment.ext.toLowerCase();
                    if (['.jpg', '.jpeg', '.png', '.gif'].includes(ext)) {
                        trueFetchedImages++;
                    } else if (['.webm', '.mp4'].includes(ext)) {
                        trueFetchedVideos++;
                    }
                }
            });
            fetchedImagesInThread = trueFetchedImages;
            fetchedVideosInThread = trueFetchedVideos;


            consoleLog(`[fetchThreadMessages] Processed thread ${threadId}: ${fetchedMessagesInThread} msgs, ${fetchedImagesInThread} imgs, ${fetchedVideosInThread} vids. Stored: ${newlyStoredImagesInThread} imgs, ${newlyStoredVideosInThread} vids.`);
            return {
                messages: processedMessages,
                counts: {
                    fetchedMessages: fetchedMessagesInThread,
                    fetchedImages: fetchedImagesInThread,
                    fetchedVideos: fetchedVideosInThread,
                    newlyStoredImages: newlyStoredImagesInThread,
                    newlyStoredVideos: newlyStoredVideosInThread
                }
            };
        } catch (error) {
            consoleError(`fetchThreadMessages error for thread ${threadId}:`, error);
            return { messages: [], counts: { fetchedMessages: 0, fetchedImages: 0, fetchedVideos: 0, newlyStoredImages: 0, newlyStoredVideos: 0 } }; // Return new structure on error
        }
    }

async function backgroundRefreshThreadsAndMessages(options = {}) { // Added options parameter
        const { skipViewerUpdate = false, isBackground = false } = options; // Destructure with default

        if (isManualRefreshInProgress) {
            consoleLog('[BG] Manual refresh in progress, skipping background refresh.');
            return;
        }
        consoleLog('[BG] Performing background refresh...', { isBackground, options });
        try {
            consoleLog('[BG] Calling scanCatalog...');
            const foundThreads = await scanCatalog();
            if (isManualRefreshInProgress) { consoleLog('[BG] Aborting due to manual refresh starting during catalog scan.'); return; }
            const foundIds = new Set(foundThreads.map(t => Number(t.id)));
            consoleLog(`[BG] scanCatalog found ${foundThreads.length} threads:`, Array.from(foundIds));

            const previousActiveThreadIds = new Set(activeThreads.map(id => Number(id)));
            consoleLog('[BG] Previous active threads:', Array.from(previousActiveThreadIds));

            // A thread is considered 'live' if it's in the catalog scan.
            // Threads that are no longer in the catalog are removed from the active list,
            // but their messages are retained.
            const liveThreadIds = new Set(foundThreads.map(t => Number(t.id)));

            // Add new threads
            liveThreadIds.forEach(threadId => {
                if (!previousActiveThreadIds.has(threadId)) {
                    consoleLog(`[BG] Adding new live thread ${threadId} from catalog scan.`);
                    activeThreads.push(threadId);
                }
            });

            // Remove non-live threads from activeThreads
            const threadsBeforePruning = activeThreads.length;
            activeThreads = activeThreads.filter(threadId => liveThreadIds.has(threadId));
            const threadsAfterPruning = activeThreads.length;

            if (threadsBeforePruning > threadsAfterPruning) {
                consoleLog(`[BG] Pruned ${threadsBeforePruning - threadsAfterPruning} non-live threads from the active list.`);
            }
            consoleLog(`[BG] Active threads after catalog sync: ${activeThreads.length}`, activeThreads);

            const fetchPromisesBg = activeThreads.map(threadId => {
                return fetchThreadMessages(threadId)
                    .then(result => ({ threadId, messages: result, status: 'fulfilled' }))
                    .catch(error => ({ threadId, error, status: 'rejected' }));
            });

            const resultsBg = await Promise.all(fetchPromisesBg);
            if (isManualRefreshInProgress) { consoleLog('[BG] Aborting due to manual refresh starting during message fetch.'); return; }

            let newMessages = [];
            resultsBg.forEach(result => {
                // consoleLog('[DebugRefreshV2][BG] backgroundRefresh - Raw Promise.allSettled result:', JSON.stringify(result)); // Removed
                if (result.status === 'fulfilled' && result) {
                    // consoleLog('[DebugRefreshV2][BG] backgroundRefresh - Fulfilled promise value:', JSON.stringify(result.value)); // Removed
                    const { threadId, messages: newMessagesResult, status: fetchStatus } = result;
                    // consoleLog('[DebugRefreshV2][BG] backgroundRefresh - Destructured - threadId:', threadId, 'fetchStatus (from wrapper):', fetchStatus, 'newMessages type:', typeof newMessages, 'is Array?:', Array.isArray(newMessages), 'length (if array):', Array.isArray(newMessages) ? newMessages.length : 'N/A'); // Removed

                    if (fetchStatus === 'rejected') {
                        consoleError(`[BG] Error fetching thread ${threadId}:`, result.error);
                        return;
                    }

                    // consoleLog(`[BG] Processing fetched messages for thread ${threadId}. Result:`, newMessages); // Original log
                    // consoleLog('[DebugRefreshV2][BG] backgroundRefresh - About to process newMessages for thread:', threadId, 'Value:', JSON.stringify(newMessages)); // Removed

                    // Handle 'not_modified' status from fetchThreadMessages
                    if (newMessagesResult && typeof newMessagesResult === 'object' && newMessagesResult.status === 'not_modified' && newMessagesResult.threadId === threadId) {
                        consoleLog(`[BG] Thread ${threadId} was not modified. Skipping message update for this thread.`);
                    } else if (newMessagesResult && Array.isArray(newMessagesResult.messages) && newMessagesResult.messages.length > 0) { // Regular message array
                        // consoleLog(`[DebugRefreshV2][BG] backgroundRefresh - Processing ${newMessages.length} messages for thread ${threadId}.`); // Removed
                        consoleLog(`[BG] Processing ${newMessagesResult.messages.length} messages for thread ${threadId}.`); // Standard log
                        let existing = messagesByThreadId[threadId] || [];
                        let existingIds = new Set(existing.map(m => m.id));
                        let updatedMessages = [...existing];
                        let newMessagesInThread = [];
                        newMessagesResult.messages.forEach(m => {
                            if (!existingIds.has(m.id)) {
                                updatedMessages.push(m);
                                newMessagesInThread.push(m);
                            }
                        });
                        newMessages.push(...newMessagesInThread);
                        updatedMessages.sort((a, b) => a.time - b.time);
                        messagesByThreadId[threadId] = updatedMessages;
                        if (messagesByThreadId[threadId].length > 0 && (!messagesByThreadId[threadId][0].title || messagesByThreadId[threadId][0].title === `Thread ${threadId}`)) {
                            messagesByThreadId[threadId][0].title = newMessagesResult.messages[0].title;
                        }
                    } else if (newMessagesResult && newMessagesResult.messages.length === 0) {
                        consoleLog(`[BG] No new messages returned or thread is empty for active thread ${threadId}.`);
                        // Note: Thread pruning logic based on catalog scan is primary.
                        // If fetchThreadMessages returns empty for a 404, it might have been removed from activeThreads already by catalog logic.
                        // If it's still active here, it means the catalog saw it, but it's empty or was just pruned.
                        // We don't remove it from activeThreads here solely based on empty messages if catalog still lists it.
                        // The original logic to remove from activeThreads if no messages returned was a bit aggressive here.
                        // The catalog scan is the authority for active threads.
                    }
                } else if (result.status === 'rejected') {
                    consoleError(`[BG] Promise rejected for a thread fetch operation:`, result.reason);
                }
            });

            consoleLog(`[BG] Final active threads after message processing: ${activeThreads.length}`, activeThreads);
            consoleLog('[BG] Saving data...');
            consoleLog("[BG] messagesByThreadId before save: ", messagesByThreadId);
            localStorage.setItem(THREADS_KEY, JSON.stringify(activeThreads));
            for (const threadId of activeThreads) {
                if (messagesByThreadId[threadId]) {
                    await saveMessagesToDB(threadId, messagesByThreadId[threadId]);
                }
            }
            localStorage.setItem(COLORS_KEY, JSON.stringify(threadColors));

            if (isManualRefreshInProgress) { consoleLog('[BG] Aborting due to manual refresh starting during data save.'); return; }

            consoleLog('[BG] Data saved. Dispatching otkMessagesUpdated event.');
            window.dispatchEvent(new CustomEvent('otkMessagesUpdated'));
            renderThreadList();

            // Calculate new messages and media from this refresh
            let newMessagesThisRefresh = newMessages.length;
            let newImagesThisRefresh = 0;
            let newVideosThisRefresh = 0;
            newMessages.forEach(msg => {
                if (msg.attachment) {
                    const ext = msg.attachment.ext.toLowerCase();
                    if (['.jpg', '.jpeg', '.png', '.gif'].includes(ext)) newImagesThisRefresh++;
                    else if (['.webm', '.mp4'].includes(ext)) newVideosThisRefresh++;
                }
            });

            // Accumulate new counts
            let accumulatedNewMessages = parseInt(localStorage.getItem('otkNewMessagesCount') || '0') + newMessagesThisRefresh;
            let accumulatedNewImages = parseInt(localStorage.getItem('otkNewImagesCount') || '0') + newImagesThisRefresh;
            let accumulatedNewVideos = parseInt(localStorage.getItem('otkNewVideosCount') || '0') + newVideosThisRefresh;

            localStorage.setItem('otkNewMessagesCount', accumulatedNewMessages);
            localStorage.setItem('otkNewImagesCount', accumulatedNewImages);
            localStorage.setItem('otkNewVideosCount', accumulatedNewVideos);

            // **FIX: Declare viewerIsOpen before it is used.**
            const viewerIsOpen = otkViewer && otkViewer.style.display === 'block';

            updateDisplayedStatistics(isBackground);

            if (viewerIsOpen && !skipViewerUpdate) {
                if (newMessages.length > 0) {
                    const cachedIds = new Set(cachedNewMessages.map(m => m.id));
                    const messagesToCache = newMessages.filter(m => !cachedIds.has(m.id));
                    cachedNewMessages.push(...messagesToCache);
                    consoleLog(`[BG] Viewer is open, caching ${messagesToCache.length} new messages for manual refresh.`);
                }
            }

            if (!viewerIsOpen) {
                consoleLog('[BG Refresh] Viewer is closed. Resynchronizing display snapshot with ground truth.');
                const allMessages = getAllMessagesSorted();

                renderedMessageIdsInViewer.clear();
                uniqueImageViewerHashes.clear();
                viewerTopLevelAttachedVideoHashes.clear();
                viewerTopLevelEmbedIds.clear();

                allMessages.forEach(message => {
                    renderedMessageIdsInViewer.add(message.id);
                    if (message.attachment) {
                        const filehash = message.attachment.filehash_db_key || `${message.attachment.tim}${message.attachment.ext}`;
                        const extLower = message.attachment.ext.toLowerCase();
                        if (['.jpg', '.jpeg', '.png', '.gif'].includes(extLower)) {
                            uniqueImageViewerHashes.add(filehash);
                        } else if (['.webm', '.mp4'].includes(extLower)) {
                            viewerTopLevelAttachedVideoHashes.add(filehash);
                        }
                    }
                    if (message.text) {
                        const inlineYoutubePatterns = [
                            { type: 'watch', regex: /(?:https?:\/\/)?(?:www\.)?youtube\.com\/watch\?(?:[^#&?\s]*&)*v=([a-zA-Z0-9_-]+)/g },
                            { type: 'short', regex: /(?:https?:\/\/)?(?:www\.)?youtube\.com\/shorts\/([a-zA-Z0-9_-]+)/g },
                            { type: 'youtu.be', regex: /(?:https?:\/\/)?youtu\.be\/([a-zA-Z0-9_-]+)/g }
                        ];
                        const inlineTwitchPatterns = [
                             { type: 'clip_direct', regex: /(?:https?:\/\/)?clips\.twitch\.tv\/([a-zA-Z0-9_-]+)/g },
                             { type: 'clip_channel', regex: /(?:https?:\/\/)?(?:www\.)?twitch\.tv\/[a-zA-Z0-9_]+\/clip\/([a-zA-Z0-9_-]+)/g },
                             { type: 'vod', regex: /(?:https?:\/\/)?(?:www\.)?twitch\.tv\/videos\/(\d+)/g }
                        ];
                        const inlineStreamablePatterns = [
                            { type: 'video', regex: /(?:https?:\/\/)?streamable\.com\/([a-zA-Z0-9]+)/g }
                        ];

                        const allPatterns = [...inlineYoutubePatterns, ...inlineTwitchPatterns, ...inlineStreamablePatterns];
                        allPatterns.forEach(patternInfo => {
                            let match;
                            while ((match = patternInfo.regex.exec(message.text)) !== null) {
                                const id = match[1];
                                if (id) {
                                    let canonicalEmbedId;
                                    if (patternInfo.type.startsWith('watch') || patternInfo.type.startsWith('short') || patternInfo.type.startsWith('youtu.be')) {
                                        canonicalEmbedId = `youtube_${id}`;
                                    } else if (patternInfo.type.startsWith('clip') || patternInfo.type.startsWith('vod')) {
                                         canonicalEmbedId = `twitch_${patternInfo.type}_${id}`;
                                    } else {
                                        canonicalEmbedId = `streamable_${id}`;
                                    }
                                    viewerTopLevelEmbedIds.add(canonicalEmbedId);
                                }
                            }
                        });
                    }
                });
                consoleLog(`[BG Refresh] Resync complete. Snapshot counts: ${renderedMessageIdsInViewer.size} msgs, ${uniqueImageViewerHashes.size} imgs, ${viewerTopLevelAttachedVideoHashes.size + viewerTopLevelEmbedIds.size} videos.`);
                updateDisplayedStatistics(); // Re-run stats update after sync
            }

            consoleLog('[BG] Background refresh complete.');

        } catch (error) {
            consoleError('[BG] Error during background refresh:', error.message, error.stack);
        }
    }

    async function refreshThreadsAndMessages(options = {}) { // Manual Refresh / Called by Clear
        const { skipViewerUpdate = false, isChildCall = false } = options; // Destructure with default

        if (!isChildCall) {
            if (isManualRefreshInProgress) {
                consoleLog('[Manual] Refresh already in progress. Ignoring top-level call.');
                return;
            }
            isManualRefreshInProgress = true;
            resetStatAnimations();
        }

        consoleLog('[Manual] Refreshing threads and messages...', { options });
        showLoadingScreen("Initializing refresh..."); // Initial message
        try {
            await new Promise(resolve => setTimeout(resolve, 50)); // Ensure loading screen renders

            updateLoadingProgress(5, "Scanning catalog for OTK threads...");
            const foundThreads = await scanCatalog();
            const foundIds = new Set(foundThreads.map(t => Number(t.id)));
            consoleLog(`[Manual] scanCatalog found ${foundThreads.length} threads:`, Array.from(foundIds));
            updateLoadingProgress(10, `Catalog scan complete. Found ${foundThreads.length} OTK threads. Syncing with local list...`);

            const previousActiveThreadIds = new Set(activeThreads.map(id => Number(id)));
            let threadsToFetch = []; // Store actual threadIds to fetch

            // A thread is considered 'live' if it's in the catalog scan.
            // Threads that are no longer in the catalog are removed from the active list,
            // but their messages are retained.
            const liveThreadIds = new Set(foundThreads.map(t => Number(t.id)));

            // Add new threads to activeThreads
            liveThreadIds.forEach(threadId => {
                if (!previousActiveThreadIds.has(threadId)) {
                    consoleLog(`[Manual] Adding new live thread ${threadId} to active list.`);
                    activeThreads.push(threadId);
                }
            });

            // Remove non-live threads from activeThreads
            const threadsBeforePruning = activeThreads.length;
            activeThreads = activeThreads.filter(threadId => liveThreadIds.has(threadId));
            const threadsAfterPruning = activeThreads.length;
            if (threadsBeforePruning > threadsAfterPruning) {
                consoleLog(`[Manual] Pruned ${threadsBeforePruning - threadsAfterPruning} non-live threads from the active list.`);
            }

            // threadsToFetch should be all live threads to ensure they are all updated.
            threadsToFetch = Array.from(liveThreadIds);

            consoleLog(`[Manual] Active threads after catalog sync: ${activeThreads.length}`, activeThreads);
            consoleLog(`[Manual] Threads to fetch this cycle: ${threadsToFetch.length}`, threadsToFetch);
            updateLoadingProgress(15, `Preparing to fetch data for ${threadsToFetch.length} threads...`);

            let totalNewMessagesThisRefresh = 0;
            let totalNewImagesThisRefresh = 0; // Fetched images
            let totalNewVideosThisRefresh = 0; // Fetched videos
            let totalImagesStoredThisRefresh = 0;
            let totalVideosStoredThisRefresh = 0;

            let threadsProcessedCount = 0;
            const totalThreadsToProcess = threadsToFetch.length;

        let newMessagesToAppend = [];
            // Use a sequential loop for fetching to update loading screen more granularly per thread
            for (const threadId of threadsToFetch) {
                threadsProcessedCount++;
                const progressPercentage = 15 + Math.round((threadsProcessedCount / totalThreadsToProcess) * 75); // 15% (catalog) + 75% (fetching/processing)

                let statusText = `Processing thread ${threadsProcessedCount}/${totalThreadsToProcess} (ID: ${threadId})...`;
                // Removed detailed message/media counts from this loading screen update
                updateLoadingProgress(progressPercentage, statusText);

                try {
                    const result = await fetchThreadMessages(threadId); // fetchThreadMessages is already async

                    if (result.status === 'not_modified') {
                        consoleLog(`[Manual] Thread ${threadId} not modified. Skipping message update.`);
                        continue; // Next thread
                    }

                    const newMessagesData = result.messages; // This is an array of message objects
                    const counts = result.counts;

                    if (Array.isArray(newMessagesData)) {
                        let actualNewMessagesInThread = 0;
                        if (newMessagesData.length > 0) {
                            let existing = messagesByThreadId[threadId] || [];
                            let existingIds = new Set(existing.map(m => m.id));
                            let updatedMessages = [...existing];
                            newMessagesData.forEach(m => {
                                if (!existingIds.has(m.id)) {
                                    updatedMessages.push(m);
                                newMessagesToAppend.push(m);
                                    actualNewMessagesInThread++;
                                }
                            });
                            updatedMessages.sort((a, b) => a.time - b.time);
                            messagesByThreadId[threadId] = updatedMessages;
                            if (messagesByThreadId[threadId].length > 0 && (!messagesByThreadId[threadId][0].title || messagesByThreadId[threadId][0].title === `Thread ${threadId}`)) {
                                messagesByThreadId[threadId][0].title = newMessagesData[0].title;
                            }
                        }
                        totalNewMessagesThisRefresh += actualNewMessagesInThread;
                        totalNewImagesThisRefresh += counts.fetchedImages;
                        totalNewVideosThisRefresh += counts.fetchedVideos;
                        totalImagesStoredThisRefresh += counts.newlyStoredImages;
                        totalVideosStoredThisRefresh += counts.newlyStoredVideos;

                        consoleLog(`[Manual] Processed thread ${threadId}. Fetched: ${counts.fetchedMessages} msgs, ${counts.fetchedImages} imgs, ${counts.fetchedVideos} vids. Added: ${actualNewMessagesInThread} new msgs. Stored: ${counts.newlyStoredImages} imgs, ${counts.newlyStoredVideos} vids.`);
                    }
                } catch (error) {
                    consoleError(`[Manual] Error processing thread ${threadId} in loop:`, error);
                    // Continue to next thread
                }
            }

            // Final update to loading screen after loop
            let finalStatusText = `Refresh processing complete. Finalizing...`; // Simplified
            updateLoadingProgress(90, finalStatusText);


    // Re-filter activeThreads based on whether messagesByThreadId still has entries for them
    // This was previously commented out as too aggressive. Catalog scan is primary.
    // However, catalog scan is the main authority. This step might be redundant if catalog scan is robust.
    // For now, let's assume catalog scan + the processing logic above correctly maintains activeThreads.
    // activeThreads = activeThreads.filter(id => messagesByThreadId[id] && messagesByThreadId[id].length > 0);
    // This filtering above is too aggressive. A thread can be active and have 0 messages temporarily.
    // The main pruning of activeThreads happens after catalog scan.

    consoleLog(`[Manual] Final active threads after message processing: ${activeThreads.length}`, activeThreads);
            consoleLog("[Manual] messagesByThreadId before save: ", messagesByThreadId);
    localStorage.setItem(THREADS_KEY, JSON.stringify(activeThreads)); // activeThreads is already updated by catalog sync
            for (const threadId of activeThreads) {
                if (messagesByThreadId[threadId]) {
                    await saveMessagesToDB(threadId, messagesByThreadId[threadId]);
                }
            }
            localStorage.setItem(COLORS_KEY, JSON.stringify(threadColors));

            consoleLog('[Manual] Core refresh actions complete.');
            updateLoadingProgress(95, "Finalizing data and updating display...");
            renderThreadList();
            window.dispatchEvent(new CustomEvent('otkMessagesUpdated'));

            // After a manual refresh, the "last seen" counts should become the new ground truth totals.
            let newTotalMessages = 0;
            let newTotalImages = 0;
            let newTotalVideos = 0;
            for (const threadId in messagesByThreadId) {
                const messages = messagesByThreadId[threadId] || [];
                newTotalMessages += messages.length;
                messages.forEach(msg => {
                    if (msg.attachment) {
                        const ext = msg.attachment.ext.toLowerCase();
                        if (['.jpg', '.jpeg', '.png', '.gif'].includes(ext)) newTotalImages++;
                        else if (['.webm', '.mp4'].includes(ext)) newTotalVideos++;
                    }
                });
            }
            localStorage.setItem(LAST_SEEN_MESSAGES_KEY, newTotalMessages);
            localStorage.setItem(LAST_SEEN_IMAGES_KEY, newTotalImages);
            localStorage.setItem(LAST_SEEN_VIDEOS_KEY, newTotalVideos);
            localStorage.setItem('otkNewMessagesCount', '0');
            localStorage.setItem('otkNewImagesCount', '0');
            localStorage.setItem('otkNewVideosCount', '0');
            consoleLog(`[Manual Refresh] Updated last seen counts and reset accumulated new counts.`);

        let viewerIsOpen = otkViewer && otkViewer.style.display === 'block';

        if (!viewerIsOpen) {
            consoleLog('[Manual Refresh] Viewer is closed. Resynchronizing display snapshot with ground truth.');
            // This is the key fix: Resync the "Display Snapshot" sets with the "Ground Truth"
            // when a manual refresh is performed with the viewer closed.

            // 1. Recalculate the "Ground Truth" from all stored messages.
            const allMessages = getAllMessagesSorted();

            // 2. Clear the "Display Snapshot" sets.
            renderedMessageIdsInViewer.clear();
            uniqueImageViewerHashes.clear();
            viewerTopLevelAttachedVideoHashes.clear();
            viewerTopLevelEmbedIds.clear();

            // 3. Repopulate the "Display Snapshot" sets with the "Ground Truth".
            allMessages.forEach(message => {
                renderedMessageIdsInViewer.add(message.id);
                if (message.attachment) {
                    const filehash = message.attachment.filehash_db_key || `${message.attachment.tim}${message.attachment.ext}`;
                    const extLower = message.attachment.ext.toLowerCase();
                    if (['.jpg', '.jpeg', '.png', '.gif'].includes(extLower)) {
                        uniqueImageViewerHashes.add(filehash);
                    } else if (['.webm', '.mp4'].includes(extLower)) {
                        viewerTopLevelAttachedVideoHashes.add(filehash);
                    }
                }
                // This logic DOES now account for embeds in the text, which is a massive improvement
                // and aligns with the primary goal of syncing the main stats.
                if (message.text) {
                    const inlineYoutubePatterns = [
                        { type: 'watch', regex: /(?:https?:\/\/)?(?:www\.)?youtube\.com\/watch\?(?:[^#&?\s]*&)*v=([a-zA-Z0-9_-]+)/g },
                        { type: 'short', regex: /(?:https?:\/\/)?(?:www\.)?youtube\.com\/shorts\/([a-zA-Z0-9_-]+)/g },
                        { type: 'youtu.be', regex: /(?:https?:\/\/)?youtu\.be\/([a-zA-Z0-9_-]+)/g }
                    ];
                    const inlineTwitchPatterns = [
                         { type: 'clip_direct', regex: /(?:https?:\/\/)?clips\.twitch\.tv\/([a-zA-Z0-9_-]+)/g },
                         { type: 'clip_channel', regex: /(?:https?:\/\/)?(?:www\.)?twitch\.tv\/[a-zA-Z0-9_]+\/clip\/([a-zA-Z0-9_-]+)/g },
                         { type: 'vod', regex: /(?:https?:\/\/)?(?:www\.)?twitch\.tv\/videos\/(\d+)/g }
                    ];
                    const inlineStreamablePatterns = [
                        { type: 'video', regex: /(?:https?:\/\/)?streamable\.com\/([a-zA-Z0-9]+)/g }
                    ];

                    const allPatterns = [...inlineYoutubePatterns, ...inlineTwitchPatterns, ...inlineStreamablePatterns];
                    allPatterns.forEach(patternInfo => {
                        let match;
                        while ((match = patternInfo.regex.exec(message.text)) !== null) {
                            const id = match[1];
                            if (id) {
                                let canonicalEmbedId;
                                if (patternInfo.type.startsWith('watch') || patternInfo.type.startsWith('short') || patternInfo.type.startsWith('youtu.be')) {
                                    canonicalEmbedId = `youtube_${id}`;
                                } else if (patternInfo.type.startsWith('clip') || patternInfo.type.startsWith('vod')) {
                                     canonicalEmbedId = `twitch_${patternInfo.type}_${id}`;
                                } else {
                                    canonicalEmbedId = `streamable_${id}`;
                                }
                                viewerTopLevelEmbedIds.add(canonicalEmbedId);
                            }
                        }
                    });
                }
            });
             consoleLog(`[Manual Refresh] Resync complete. Snapshot counts: ${renderedMessageIdsInViewer.size} msgs, ${uniqueImageViewerHashes.size} imgs, ${viewerTopLevelAttachedVideoHashes.size + viewerTopLevelEmbedIds.size} videos.`);
        }

            updateDisplayedStatistics(false);

        if (!skipViewerUpdate && viewerIsOpen) {
            let allNewMessages = [...cachedNewMessages, ...newMessagesToAppend];
            cachedNewMessages = [];
            consoleLog('[Manual Refresh] Cleared background message cache.');
            const allNewIds = new Set();
            const uniqueNewMessages = allNewMessages.filter(m => {
                if (allNewIds.has(m.id)) {
                    return false;
                }
                allNewIds.add(m.id);
                return true;
            });
            const finalMessagesToAppend = uniqueNewMessages.filter(m => !renderedMessageIdsInViewer.has(m.id));
            consoleLog(`[Manual Refresh] Viewer is open, appending ${finalMessagesToAppend.length} new messages.`);
            await appendNewMessagesToViewer(finalMessagesToAppend);
        } else {
            consoleLog(`[Manual Refresh] Viewer not updated. Skip viewer update: ${skipViewerUpdate}, Viewer is open: ${viewerIsOpen}`);
        }
            // If viewer is not open, no specific viewer update action here, it will populate on next open.

            updateLoadingProgress(100, "Refresh complete!");
            setTimeout(hideLoadingScreen, 500);

        } catch (error) {
            consoleError('[Manual] Error during core refresh:', error);
            updateLoadingProgress(100, "Error during refresh. Check console.");
            setTimeout(hideLoadingScreen, 1500); // Keep error message visible a bit longer
        } finally {
            if (!isChildCall) {
                isManualRefreshInProgress = false;
            }
        }
    }

    async function clearAndRefresh() {
        consoleLog('[Clear] Clear and Refresh initiated...');
        resetStatAnimations();
        const viewerWasOpen = otkViewer && otkViewer.style.display === 'block';

        // Clear viewer content and related state immediately if viewer was open
        if (viewerWasOpen) {
            consoleLog('[Clear] Viewer was open, clearing its content and state immediately.');
            otkViewer.innerHTML = ''; // Clear existing viewer DOM
            renderedMessageIdsInViewer.clear(); // Clear the set of rendered message IDs
            uniqueImageViewerHashes.clear();
            viewerTopLevelAttachedVideoHashes.clear();
            viewerTopLevelEmbedIds.clear();
            renderedFullSizeImageHashes.clear();
            viewerActiveImageCount = null; // Reset viewer-specific counts
            viewerActiveVideoCount = null;
            lastViewerScrollTop = 0; // Reset scroll position memory
        }

        isManualRefreshInProgress = true;
        try {
            activeThreads = [];
            messagesByThreadId = {};
            threadColors = {};
            blockedThreads = new Set();
            localStorage.removeItem(THREADS_KEY);
            // No longer need to remove MESSAGES_KEY, as it's not used.
            localStorage.removeItem(COLORS_KEY);
            localStorage.removeItem(DROPPED_THREADS_KEY);
            localStorage.removeItem(SEEN_EMBED_URL_IDS_KEY);
            localStorage.setItem(LOCAL_IMAGE_COUNT_KEY, '0');
            localStorage.setItem(LOCAL_VIDEO_COUNT_KEY, '0');
            localStorage.removeItem(LAST_SEEN_MESSAGES_KEY);
            localStorage.removeItem(LAST_SEEN_IMAGES_KEY);
            localStorage.removeItem(LAST_SEEN_VIDEOS_KEY);
            localStorage.removeItem(BLOCKED_THREADS_KEY);
            consoleLog('[Clear] LocalStorage (threads, messages, seen embeds, media counts, ACTIVE theme) cleared/reset. CUSTOM THEMES PRESERVED.');

            if (otkMediaDB) {
                consoleLog('[Clear] Clearing IndexedDB mediaStore (preserving filtered media)...');
                const filterRules = JSON.parse(localStorage.getItem(FILTER_RULES_V2_KEY) || '[]');
                const preservedHashes = new Set();

                filterRules.forEach(rule => {
                    let mediaHash = null;
                    if (rule.category === 'attachedMedia' && rule.matchContent) {
                        mediaHash = rule.matchContent.replace('md5:', '');
                    } else if (rule.category === 'entireMessage' && rule.matchContent) {
                        try {
                            const conditions = JSON.parse(rule.matchContent);
                            if (conditions.media) {
                                mediaHash = conditions.media.replace('md5:', '');
                            }
                        } catch (err) {
                            consoleError(`[Clear] Failed to parse media hash from 'entireMessage' rule:`, rule.matchContent, err);
                        }
                    }

                    if (mediaHash) {
                        preservedHashes.add(mediaHash);
                        preservedHashes.add(`${mediaHash}_thumb`); // Also preserve the thumbnail
                    }
                });

                consoleLog(`[Clear] Preserving ${preservedHashes.size} media files (including thumbnails) from filter rules.`);

                const mediaTransaction = otkMediaDB.transaction(['mediaStore'], 'readwrite');
                const mediaStore = mediaTransaction.objectStore('mediaStore');
                const cursorRequest = mediaStore.openCursor();

                await new Promise((resolve, reject) => {
                    cursorRequest.onsuccess = (event) => {
                        const cursor = event.target.result;
                        if (cursor) {
                            if (!preservedHashes.has(cursor.key)) {
                                cursor.delete();
                            }
                            cursor.continue();
                        } else {
                            resolve(); // Cursor finished
                        }
                    };
                    cursorRequest.onerror = (event) => {
                        consoleError('[Clear] Error while clearing mediaStore with cursor:', event.target.error);
                        reject(event.target.error);
                    };
                });

                const messagesTransaction = otkMediaDB.transaction(['messagesStore'], 'readwrite');
                const messagesStore = messagesTransaction.objectStore('messagesStore');
                const messagesClearRequest = messagesStore.clear();
                await new Promise((resolve, reject) => {
                    messagesClearRequest.onsuccess = () => {
                        consoleLog('[Clear] IndexedDB messagesStore cleared successfully.');
                        resolve();
                    };
                    messagesClearRequest.onerror = (event) => {
                        consoleError('[Clear] Error clearing IndexedDB messagesStore:', event.target.error);
                        reject(event.target.error);
                    };
                });
            } else {
                consoleWarn('[Clear] otkMediaDB not initialized, skipping IndexedDB clear.');
            }

            consoleLog('[Clear] Calling refreshThreadsAndMessages to repopulate data (viewer updates will be skipped by refresh function)...');
            await refreshThreadsAndMessages({ skipViewerUpdate: true, isChildCall: true });

            // Explicitly re-render the viewer if it was open, using the fresh data.
            if (viewerWasOpen) {
                consoleLog('[Clear] Re-rendering viewer with fresh data after clear.');
                await renderMessagesInViewer({ isToggleOpen: false }); // isToggleOpen: false typically scrolls to bottom or default.
            }
            // window.dispatchEvent(new CustomEvent('otkClearViewerDisplay')); // Removed as direct render is now handled.
            consoleLog('[Clear] Clear and Refresh data processing complete.');
        } catch (error) {
            consoleError('[Clear] Error during clear and refresh:', error);
        } finally {
            isManualRefreshInProgress = false;
            consoleLog('[Clear] Manual refresh flag reset.');
            renderThreadList(); // Update GUI bar with (now minimal) live threads
            updateDisplayedStatistics(); // Update stats based on cleared and re-fetched data
        }
    }


    function ensureViewerExists() {
        if (!document.getElementById('otk-viewer')) {
            otkViewer = document.createElement('div');
            otkViewer.id = 'otk-viewer';
            document.body.appendChild(otkViewer);
            consoleLog('Viewer element created.');
        } else {
            otkViewer = document.getElementById('otk-viewer');
            consoleLog('Viewer element already exists.');
        }

        otkViewer.style.cssText = `
            position: fixed;
            top: 86px;
            left: 0;
            width: 100vw;
            height: calc(100vh - 86px);
            bottom: 0;
            /* background-color: #181818; */ /* New background color - replaced by variable below */
            opacity: 1; /* Ensure full opacity */
            z-index: 9998;
            /* overflow-y: hidden; */ /* Ensure viewer itself doesn't show scrollbars */
            box-sizing: border-box;
            background-color: var(--otk-viewer-bg-color); /* Original viewer background */
            color: var(--otk-gui-text-color); /* Viewer default text color, can be same as GUI or new variable later */
            padding: 0; /* No padding, will be handled by messagesContainer */
            border-top: 1px solid #181818; /* Assuming border might be different or themed later, keep for now */
            display: none;
            overflow-x: hidden; /* Prevent horizontal scrollbar on the viewer itself */
        `;
        consoleLog("Applied basic styling to otkViewer: background #181818, default text color #e6e6e6, padding (0), border-top #181818, overflow-x: hidden.");
    }

    function toggleViewer() {
        if (!otkViewer) {
            consoleWarn('Viewer element not found. Attempting to create.');
            ensureViewerExists();
            if (!otkViewer) {
                consoleError('Viewer element could not be initialized.');
                return;
            }
        }

        const isViewerVisible = otkViewer.style.display !== 'none';
        if (isViewerVisible) {
            const messagesContainer = document.getElementById('otk-messages-container');
            if (messagesContainer) {
                lastViewerScrollTop = messagesContainer.scrollTop;
                consoleLog(`Viewer closed. Scroll position saved: ${lastViewerScrollTop}`);
            }
            otkViewer.style.display = 'none';
            document.body.style.overflow = 'auto';
            localStorage.setItem(VIEWER_OPEN_KEY, 'false');
            for (const url of createdBlobUrls) {
                URL.revokeObjectURL(url);
            }
            createdBlobUrls.clear();
            consoleLog('Viewer hidden state saved to localStorage.');
            // Reset viewer-specific counts and update stats to reflect totals
            viewerActiveImageCount = null;
            viewerActiveVideoCount = null;
            updateDisplayedStatistics();
        } else {
            otkViewer.style.display = 'block';
            document.body.style.overflow = 'hidden';
            localStorage.setItem(VIEWER_OPEN_KEY, 'true');
            consoleLog('Viewer shown. State saved to localStorage. Applying layout and rendering all messages.');

            // Apply correct layout class before rendering
            otkViewer.classList.add('otk-message-layout-default');
            otkViewer.classList.remove('otk-message-layout-newdesign');
            // renderMessagesInViewer will calculate and set viewerActive counts and then call updateDisplayedStatistics
            renderMessagesInViewer({isToggleOpen: true}); // Pass flag
        }
    }

    function resetStatAnimations() {
        // Stop all active animation timers
        statAnimationTimers.forEach(timerId => clearInterval(timerId));
        statAnimationTimers = []; // Clear the array

        // Hide the (+n) elements
        const newStatSpans = document.querySelectorAll('.new-stat');
        newStatSpans.forEach(span => {
            span.textContent = '';
        });

        consoleLog('All stat animations have been reset.');
    }

    function animateStat(element, startValue, targetValue) {
        const diff = targetValue - startValue;
        if (diff <= 0) {
            if (targetValue > 0) {
                element.textContent = `(+${targetValue})`;
            } else {
                element.textContent = '';
            }
            return;
        }

        if (tabHidden) {
            element.textContent = `(+${targetValue})`;
            return;
        }

        const duration = Math.min(10000, diff * 333); // Max 10 seconds, ~3 per second
        const stepTime = duration / diff;

        let current = startValue;
        const timer = setInterval(() => {
            current++;
            element.textContent = `(+${current})`;
            if (current >= targetValue) {
                clearInterval(timer);
                statAnimationTimers = statAnimationTimers.filter(t => t !== timer);
            }
        }, stepTime);
        statAnimationTimers.push(timer);
    }

    function updateDisplayedStatistics(isBackgroundUpdate = false) {
        const threadsTrackedElem = document.getElementById('otk-threads-tracked-stat');
        const totalMessagesElem = document.getElementById('otk-total-messages-stat');
        const localImagesElem = document.getElementById('otk-local-images-stat');
        const localVideosElem = document.getElementById('otk-local-videos-stat');

        if (!threadsTrackedElem || !totalMessagesElem || !localImagesElem || !localVideosElem) {
            consoleWarn('One or more statistics elements not found in GUI.');
            return;
        }

        const getOldStatValue = (id) => {
            const elem = document.getElementById(`otk-stat-new-${id}`);
            return elem ? parseInt(elem.textContent.replace(/[^\d]/g, '') || '0', 10) : 0;
        };

        const oldNewMessages = getOldStatValue('messages');
        const oldNewImages = getOldStatValue('images');
        const oldNewVideos = getOldStatValue('videos');

        let totalMessagesInStorage = 0;
        let totalImagesInStorage = 0;
        let totalVideosInStorage = 0;

        for (const threadId in messagesByThreadId) {
            const messages = messagesByThreadId[threadId] || [];
            totalMessagesInStorage += messages.length;
            messages.forEach(msg => {
                if (msg.attachment) {
                    const ext = msg.attachment.ext.toLowerCase();
                    if (['.jpg', '.jpeg', '.png', '.gif'].includes(ext)) {
                        totalImagesInStorage++;
                    } else if (['.webm', '.mp4'].includes(ext)) {
                        totalVideosInStorage++;
                    }
                }
            });
        }

        const newMessages = parseInt(localStorage.getItem('otkNewMessagesCount') || '0');
        const newImages = parseInt(localStorage.getItem('otkNewImagesCount') || '0');
        const newVideos = parseInt(localStorage.getItem('otkNewVideosCount') || '0');

        const viewerIsOpen = otkViewer && otkViewer.style.display === 'block';

        const mainMessagesCount = viewerIsOpen ? renderedMessageIdsInViewer.size : totalMessagesInStorage;
        const mainImagesCount = viewerIsOpen ? uniqueImageViewerHashes.size : totalImagesInStorage;
        const mainVideosCount = viewerIsOpen ? (viewerTopLevelAttachedVideoHashes.size + viewerTopLevelEmbedIds.size) : totalVideosInStorage;

        if(viewerIsOpen) {
            consoleLog(`[StatDebug] Viewer is OPEN. Using viewer-specific counts: Msgs=${mainMessagesCount}, Imgs=${mainImagesCount}, Vids=${mainVideosCount}`);
        } else {
            consoleLog(`[StatDebug] Viewer is CLOSED. Using total storage counts: Msgs=${mainMessagesCount}, Imgs=${mainImagesCount}, Vids=${mainVideosCount}`);
        }

        const liveThreadsCount = activeThreads.length;

        const updateStatLine = (container, baseText, newCount, startCount, id) => {
            let lineContainer = document.getElementById(`otk-stat-${id}`);
            if (!lineContainer) {
                lineContainer = document.createElement('div');
                lineContainer.id = `otk-stat-${id}`;
                lineContainer.style.display = 'flex';
                lineContainer.style.justifyContent = 'flex-start';
                lineContainer.style.width = '100%';

                const baseSpan = document.createElement('span');
                baseSpan.id = `otk-stat-base-${id}`;
                lineContainer.appendChild(baseSpan);

                const newCountSpan = document.createElement('span');
                newCountSpan.id = `otk-stat-new-${id}`;
                newCountSpan.className = 'new-stat';
                newCountSpan.style.color = 'var(--otk-background-updates-stats-text-color)';
                newCountSpan.style.marginLeft = '5px';
                lineContainer.appendChild(newCountSpan);
                container.appendChild(lineContainer);
            }

            const baseSpan = document.getElementById(`otk-stat-base-${id}`);
            baseSpan.innerHTML = ''; // Clear previous content

            const dashSpan = document.createElement('span');
            dashSpan.textContent = '• ';
            dashSpan.style.color = 'var(--otk-stats-dash-color)';

            const textNode = document.createTextNode(baseText.substring(2)); // Get text after '• '

            baseSpan.appendChild(dashSpan);
            baseSpan.appendChild(textNode);

            const newCountSpan = document.getElementById(`otk-stat-new-${id}`);
            if (newCount > 0) {
                if (isBackgroundUpdate) {
                    animateStat(newCountSpan, startCount, newCount);
                } else {
                    newCountSpan.textContent = `(+${newCount})`;
                }
            } else {
                newCountSpan.textContent = ''; // Explicitly clear if no new items
            }
        };

        const paddingLength = 4;
        updateStatLine(threadsTrackedElem, `- ${padNumber(liveThreadsCount, paddingLength)} Live Thread${liveThreadsCount === 1 ? '' : 's'}`, 0, 0, 'threads');
        updateStatLine(totalMessagesElem, `- ${padNumber(mainMessagesCount, paddingLength)} Total Message${mainMessagesCount === 1 ? '' : 's'}`, newMessages, oldNewMessages, 'messages');
        updateStatLine(localImagesElem, `- ${padNumber(mainImagesCount, paddingLength)} Image${mainImagesCount === 1 ? '' : 's'}`, newImages, oldNewImages, 'images');
        updateStatLine(localVideosElem, `- ${padNumber(mainVideosCount, paddingLength)} Video${mainVideosCount === 1 ? '' : 's'}`, newVideos, oldNewVideos, 'videos');
    }

    function setupTitleObserver() {
        const targetNode = document.getElementById('otk-stat-new-messages');
        if (!targetNode) {
            consoleError("Could not find the target node for title observer: #otk-stat-new-messages");
            return;
        }

        const observer = new MutationObserver(mutations => {
            mutations.forEach(mutation => {
                const newMessagesText = targetNode.textContent.trim();
                if (newMessagesText) {
                    document.title = `${newMessagesText} ${originalTitle}`;
                } else {
                    document.title = originalTitle;
                }
            });
        });

        observer.observe(targetNode, {
            childList: true,
            characterData: true,
            subtree: true
        });

        consoleLog("Title observer is set up and watching for changes on #otk-stat-new-messages.");
    }

    function createTrackerButton(text, id = null) {
        const button = document.createElement('button');
        if (id) button.id = id;
        button.textContent = text;
        button.classList.add('otk-tracker-button'); // Add a common class for potential shared base styles not from variables
        button.style.cssText = `
            padding: 12px 15px;
            cursor: pointer;
            background-color: var(--otk-button-bg-color);
            color: var(--otk-button-text-color);
            border: 1px solid var(--otk-button-border-color);
            border-radius: 3px;
            font-size: 13px;
            white-space: nowrap; /* Prevent button text wrapping */
            /* Transition for smooth background color change can be added here or in CSS */
            transition: background-color 0.15s ease-in-out;
        `;

        button.addEventListener('mouseover', () => {
            if (!button.disabled) { // Check if button is not disabled
                button.classList.add('otk-button--hover');
                // Fallback if CSS variables/classes somehow fail, or for non-variable parts of hover
                // button.style.backgroundColor = 'var(--otk-button-hover-bg-color)'; // Direct application as fallback/override example
            }
        });
        button.addEventListener('mouseout', () => {
            if (!button.disabled) {
                button.classList.remove('otk-button--hover');
                button.classList.remove('otk-button--active'); // Ensure active is also removed if mouse leaves while pressed
                // Fallback: reset to base color
                // button.style.backgroundColor = 'var(--otk-button-bg-color)';
            }
        });
        button.addEventListener('mousedown', () => {
            if (!button.disabled) {
                button.classList.add('otk-button--active');
                // Fallback
                // button.style.backgroundColor = 'var(--otk-button-active-bg-color)';
            }
        });
        button.addEventListener('mouseup', () => {
            if (!button.disabled) {
                button.classList.remove('otk-button--active');
                // If mouse is still over, hover effect should apply.
                // If mouseup happens outside, mouseout would have cleared hover.
                // If mouseup happens inside, it should revert to hover state if still over.
                if (button.matches(':hover')) { // Check if mouse is still over the button
                     button.classList.add('otk-button--hover');
                }
                // Fallback
                // if (button.matches(':hover')) button.style.backgroundColor = 'var(--otk-button-hover-bg-color)';
                // else button.style.backgroundColor = 'var(--otk-button-bg-color)';
            }
        });
        return button;
    }

    // --- Button Implementations & Event Listeners ---
    const clockElement = document.createElement('div');
    clockElement.id = 'otk-clock';
    clockElement.style.cssText = `
        position: fixed;
        top: 86px;
        right: 10px;
        background-color: var(--otk-clock-bg-color);
        color: var(--otk-clock-text-color, var(--otk-gui-text-color));
        padding: 5px;
        border: 1px solid var(--otk-clock-border-color);
        border-radius: 5px;
        z-index: 100001;
        display: none;
        cursor: move;
        display: flex; /* Use flexbox to align text and icon */
        align-items: center; /* Center items vertically */
    `;

    document.body.appendChild(clockElement);

    // Timezone Search Container
    const timezoneSearchContainer = document.createElement('div');
    timezoneSearchContainer.id = 'otk-timezone-search-container';
    timezoneSearchContainer.style.cssText = `
        position: fixed;
        /* Position will be set dynamically based on clock position */
        background-color: var(--otk-clock-search-bg-color, #333);
        border: 1px solid #555;
        border-radius: 4px;
        z-index: 100002; /* Above clock */
        display: none;
        padding: 8px;
        width: 250px;
    `;
    const searchInput = document.createElement('input');
    searchInput.type = 'text';
    searchInput.id = 'otk-timezone-search-input';
    searchInput.placeholder = 'Search for a city/region...';
    searchInput.style.cssText = 'width: 100%; box-sizing: border-box; margin-bottom: 5px;';
    timezoneSearchContainer.appendChild(searchInput);

    const searchResultsDiv = document.createElement('div');
    searchResultsDiv.id = 'otk-timezone-search-results';
    searchResultsDiv.style.cssText = 'max-height: 200px; overflow-y: auto;';
    timezoneSearchContainer.appendChild(searchResultsDiv);

    document.body.appendChild(timezoneSearchContainer);

    // Make clock draggable
    let isClockDragging = false;
    let clockOffsetX, clockOffsetY;

    // Load saved clock position
    const CLOCK_POSITION_KEY = 'otkClockPosition';
    try {
        const savedClockPos = JSON.parse(localStorage.getItem(CLOCK_POSITION_KEY));
        if (savedClockPos && savedClockPos.top && savedClockPos.left) {
            clockElement.style.top = savedClockPos.top;
            clockElement.style.left = savedClockPos.left;
            clockElement.style.right = 'auto';
        }
    } catch (e) {
        consoleError("Error parsing saved clock position from localStorage:", e);
    }


    clockElement.addEventListener('mousedown', (e) => {
        isClockDragging = true;
        clockOffsetX = e.clientX - clockElement.offsetLeft;
        clockOffsetY = e.clientY - clockElement.offsetTop;
        clockElement.style.userSelect = 'none';
        document.body.style.userSelect = 'none';
    });

    document.addEventListener('mousemove', (e) => {
        if (isClockDragging) {
            let newLeft = e.clientX - clockOffsetX;
            let newTop = e.clientY - clockOffsetY;

            const buffer = 10;
            const maxLeft = window.innerWidth - clockElement.offsetWidth - buffer;
            const maxTop = window.innerHeight - clockElement.offsetHeight - buffer;

            newLeft = Math.max(buffer, Math.min(newLeft, maxLeft));
            newTop = Math.max(buffer, Math.min(newTop, maxTop));

            clockElement.style.left = newLeft + 'px';
            clockElement.style.top = newTop + 'px';
            clockElement.style.right = 'auto';
        }
    });

    document.addEventListener('mouseup', () => {
        if (isClockDragging) {
            isClockDragging = false;
            clockElement.style.userSelect = '';
            document.body.style.userSelect = '';
            // Save position to localStorage
            localStorage.setItem(CLOCK_POSITION_KEY, JSON.stringify({top: clockElement.style.top, left: clockElement.style.left}));
        }
    });

    // --- Draggable Countdown Timer ---
    const countdownElement = document.createElement('div');
    countdownElement.id = 'otk-countdown-timer-movable';
    countdownElement.style.cssText = `
        position: fixed;
        top: 90px;
        left: 50%;
        transform: translateX(-50%);
        background-color: var(--otk-countdown-bg-color, var(--otk-gui-bg-color));
        padding: 5px;
        border-radius: 5px;
        z-index: 100001;
        display: flex;
        align-items: center;
        cursor: move;
        font-size: 14px;
        white-space: nowrap;
    `;
    const countdownTimer = document.createElement('span');
    countdownTimer.id = 'otk-countdown-timer';
    countdownTimer.textContent = '00:00:00';
    const countdownLabel = document.createElement('span');
    countdownLabel.id = 'otk-countdown-label';
    countdownLabel.textContent = 'Next Update:\u00A0';
    countdownLabel.style.color = 'var(--otk-countdown-label-text-color)';
    countdownTimer.style.color = 'var(--otk-countdown-timer-text-color)';
    countdownElement.appendChild(countdownLabel);
    countdownElement.appendChild(countdownTimer);
    document.body.appendChild(countdownElement);

    let isCountdownDragging = false;
    let countdownOffsetX, countdownOffsetY;

    const COUNTDOWN_POSITION_KEY = 'otkCountdownPosition';
    try {
        const savedCountdownPos = JSON.parse(localStorage.getItem(COUNTDOWN_POSITION_KEY));
        if (savedCountdownPos && savedCountdownPos.top && savedCountdownPos.left) {
            countdownElement.style.top = savedCountdownPos.top;
            countdownElement.style.left = savedCountdownPos.left;
            countdownElement.style.transform = 'none'; // Remove transform if we have a saved position
        }
    } catch (e) {
        consoleError("Error parsing saved countdown position from localStorage:", e);
    }

    countdownElement.addEventListener('mousedown', (e) => {
        isCountdownDragging = true;
        countdownOffsetX = e.clientX - countdownElement.offsetLeft;
        countdownOffsetY = e.clientY - countdownElement.offsetTop;
        countdownElement.style.userSelect = 'none';
        document.body.style.userSelect = 'none';
    });

    document.addEventListener('mousemove', (e) => {
        if (isCountdownDragging) {
            let newLeft = e.clientX - countdownOffsetX;
            let newTop = e.clientY - countdownOffsetY;

            countdownElement.style.left = newLeft + 'px';
            countdownElement.style.top = newTop + 'px';
            countdownElement.style.transform = 'none';
        }
    });

    document.addEventListener('mouseup', () => {
        if (isCountdownDragging) {
            isCountdownDragging = false;
            countdownElement.style.userSelect = '';
            document.body.style.userSelect = '';
            localStorage.setItem(COUNTDOWN_POSITION_KEY, JSON.stringify({top: countdownElement.style.top, left: countdownElement.style.left}));
        }
    });

    // Hide search if clicking outside
    document.addEventListener('click', (e) => {
        const clockOptionsWindow = document.getElementById('otk-clock-options-window');
        if (
            !clockElement.contains(e.target) &&
            !timezoneSearchContainer.contains(e.target) &&
            (!clockOptionsWindow || !clockOptionsWindow.contains(e.target))
        ) {
            timezoneSearchContainer.style.display = 'none';
        }
    });


    const buttonContainer = document.getElementById('otk-button-container');
    if (buttonContainer) {
        const btnToggleViewer = createTrackerButton('Toggle Viewer', 'otk-toggle-viewer-btn');
        btnToggleViewer.addEventListener('click', toggleViewer);
        // Appended to bottomRowContainer later

        const btnRefresh = createTrackerButton('Refresh Data', 'otk-refresh-data-btn');
        btnRefresh.addEventListener('click', async () => {
            if (isManualRefreshInProgress) {
                consoleLog('[GUI] "Refresh Data" button clicked, but a refresh is already in progress. Ignoring.');
                return; // Ignore click if a refresh is already happening
            }
            consoleLog('[GUI] "Refresh Data" button clicked.');
            // isManualRefreshInProgress is set to true at the start of refreshThreadsAndMessages
            // and false in its finally block. This prevents the race condition without disabling the button.
            try {
                await refreshThreadsAndMessages();
                consoleLog('[GUI] Data refresh complete.');
            } catch (error) {
                consoleError('[GUI] Error during data refresh:', error);
            } finally {
                stopBackgroundRefresh();
                startBackgroundRefresh();
            }
            // No finally block needed here to re-enable the button, as it's never disabled.
        });
        // Appended to bottomRowContainer later

        // Create topRowContainer for the checkbox
        const topRowContainer = document.createElement('div');
        // No specific styles for topRowContainer itself yet, alignment is handled by otk-button-container

        // Create bottomRowContainer for the buttons
        const bottomRowContainer = document.createElement('div');
        bottomRowContainer.style.cssText = `
            display: flex;
            flex-direction: row;
            gap: 10px;
            align-items: center;
        `;

        const controlsWrapper = document.createElement('div');
        controlsWrapper.style.cssText = `
            display: flex;
            flex-direction: column;
            justify-content: space-around;
            align-items: flex-start;
            gap: 4px; /* Increased gap */
            height: auto; /* Allow it to size based on content */
        `;

        // Debug mode checkbox and label are removed from here.
        // DEBUG_MODE is now only toggled via localStorage or by editing the script.

        // Countdown timer is now a separate draggable element

        const btnClearRefresh = createTrackerButton('Restart Tracker', 'otk-restart-tracker-btn');

        const btnMemoryReport = createTrackerButton('Memory Report', 'otk-memory-report-btn');
        btnMemoryReport.style.display = localStorage.getItem('otkMemoryReportEnabled') === 'true' ? 'inline-block' : 'none';
        btnMemoryReport.addEventListener('click', generateMemoryUsageReport);

        const btnFilter = createTrackerButton('Filter', 'otk-filter-btn');
        btnFilter.addEventListener('click', () => {
            const filterWindow = document.getElementById('otk-filter-window');
            if (filterWindow) {
                filterWindow.style.display = filterWindow.style.display === 'none' ? 'flex' : 'none';
            }
        });


        const thirdButtonColumn = document.createElement('div');
        thirdButtonColumn.style.cssText = `
            display: flex;          /* It's a flex container for controlsWrapper */
            flex-direction: column; /* Stack its children (controlsWrapper) */
            justify-content: center;/* Center controlsWrapper vertically */
            align-items: center;    /* Center controlsWrapper horizontally */
            /* height: 100%; Removed, let it size by content */
            /* min-width: 130px; Removed, let it size by content */
        `;
        // controlsWrapper has align-self: center and width: fit-content, which is good.
        // Ensure controlsWrapper takes appropriate width for its content (checkbox + label)
        // and centers itself within the stretched column.
        controlsWrapper.style.width = 'fit-content';
        controlsWrapper.style.alignSelf = 'center';

        thirdButtonColumn.appendChild(controlsWrapper);
        // btnClearRefresh is handled below
        // buttonContainer.appendChild(thirdButtonColumn); // This is now part of topRowContainer

        // Append elements to their respective row containers
        topRowContainer.appendChild(thirdButtonColumn);

        bottomRowContainer.appendChild(btnToggleViewer);
        bottomRowContainer.appendChild(btnRefresh);
        bottomRowContainer.appendChild(btnClearRefresh);
        bottomRowContainer.appendChild(btnFilter);
        bottomRowContainer.appendChild(btnMemoryReport);

        const btnPip = createTrackerButton('Picture-in-Picture', 'otk-pip-btn');
        btnPip.style.display = localStorage.getItem('otkPipModeEnabled') === 'true' ? 'inline-block' : 'none';
        bottomRowContainer.appendChild(btnPip);

        btnPip.addEventListener('click', () => {
            document.body.classList.toggle('otk-pip-mode');

            if (document.body.classList.contains('otk-pip-mode')) {
                enablePipMode();
            } else {
                disablePipMode();
            }
        });


        // Append row containers to the main buttonContainer
        buttonContainer.appendChild(topRowContainer);
        buttonContainer.appendChild(bottomRowContainer);

        btnClearRefresh.addEventListener('click', async () => {
            consoleLog('[GUI] "Restart Thread Tracker" button clicked.');
            if (!confirm("Are you sure you want to restart the tracker? This will clear all tracked threads, messages, and media from IndexedDB.")) {
                consoleLog('[GUI] Restart cancelled by user.');
                return;
            }
            btnClearRefresh.disabled = true;
            // isManualRefreshInProgress will be handled by clearAndRefresh
            try {
                await clearAndRefresh();
                consoleLog('[GUI] Clear and refresh sequence complete.');
            } catch (error) {
                consoleError('[GUI] Error during clear and refresh sequence:', error);
            } finally {
                btnClearRefresh.disabled = false;
                consoleLog('[GUI] Restart operation finished.');
            }
        });

    } else {
        consoleError('Button container not found. GUI buttons cannot be added.');
    }

    // --- Background Refresh Control ---
    let lastActivityTimestamp = Date.now();
    let suspensionCheckIntervalId = null;
    let countdownIntervalId = null;

    function updateCountdown() {
        const nextUpdateTimestamp = parseInt(localStorage.getItem('otkNextUpdateTimestamp') || '0', 10);
        const countdownTimer = document.getElementById('otk-countdown-timer');
        if (!countdownTimer) {
            return;
        }

        const now = Date.now();
        const timeLeft = Math.max(0, nextUpdateTimestamp - now);
        const hours = Math.floor(timeLeft / (1000 * 60 * 60));
        const minutes = Math.floor((timeLeft % (1000 * 60 * 60)) / (1000 * 60));
        const seconds = Math.floor((timeLeft % (1000 * 60)) / 1000);

        countdownTimer.textContent = `${padNumber(hours, 2)}:${padNumber(minutes, 2)}:${padNumber(seconds, 2)}`;
    }

    function startBackgroundRefresh(immediate = false) {
        if (localStorage.getItem(BACKGROUND_UPDATES_DISABLED_KEY) === 'true') {
            consoleLog('Background updates are disabled. Not starting refresh interval.');
            return;
        }
        if (backgroundRefreshIntervalId === null) { // Only start if not already running
            const minUpdateMinutes = parseInt(localStorage.getItem('otkMinUpdateSeconds') || '2', 10);
            const maxUpdateMinutes = parseInt(localStorage.getItem('otkMaxUpdateSeconds') || '5', 10);
            const minUpdateSeconds = minUpdateMinutes * 60;
            const maxUpdateSeconds = maxUpdateMinutes * 60;
            const randomIntervalSeconds = Math.floor(Math.random() * (maxUpdateSeconds - minUpdateSeconds + 1)) + minUpdateSeconds;
            let refreshIntervalMs = immediate ? 0 : randomIntervalSeconds * 1000;

            const nextUpdateTimestamp = Date.now() + refreshIntervalMs;
            localStorage.setItem('otkNextUpdateTimestamp', nextUpdateTimestamp);


            backgroundRefreshIntervalId = setTimeout(() => {
                if (isSuspended) {
                    consoleLog(`[BG] Updates suspended.`);
                    stopBackgroundRefresh();
                    showSuspendedScreen();
                    return;
                }
                backgroundRefreshThreadsAndMessages({ isBackground: true });
                backgroundRefreshIntervalId = null; // Reset for the next cycle
                startBackgroundRefresh(); // Schedule the next update
            }, refreshIntervalMs);

            if(immediate){
                consoleLog(`Background refresh started immediately.`);
            } else {
                consoleLog(`Background refresh scheduled in ${minUpdateMinutes}-${maxUpdateMinutes} minutes. Next update at ~${new Date(Date.now() + refreshIntervalMs).toLocaleTimeString()}`);
            }

            if (countdownIntervalId) {
                clearInterval(countdownIntervalId);
            }
            countdownIntervalId = setInterval(updateCountdown, 1000);
        }
    }

    function stopBackgroundRefresh() {
        if (backgroundRefreshIntervalId) {
            clearTimeout(backgroundRefreshIntervalId);
            backgroundRefreshIntervalId = null;
            consoleLog('Background refresh stopped.');
        } else {
            consoleLog('Background refresh was not running.');
        }
    }

    let activeClockSearchId = null;

    function renderClockOptions() {
        const contentArea = document.getElementById('otk-clock-options-content');
        if (!contentArea) return;

        contentArea.innerHTML = ''; // Clear previous content

        const clocks = JSON.parse(localStorage.getItem('otkClocks') || '[]');
        let draggedClockId = null;

        const clockListContainer = document.createElement('div');
        contentArea.appendChild(clockListContainer);

        clocks.forEach((clock, index) => {
            const clockRow = document.createElement('div');
            clockRow.draggable = true;
            clockRow.dataset.clockId = clock.id;
            clockRow.style.cssText = `
                display: flex;
                justify-content: space-between;
                align-items: center;
                padding: 8px 0;
                border-bottom: 1px solid #444;
                cursor: grab;
            `;

            clockRow.addEventListener('dragstart', (e) => {
                draggedClockId = clock.id;
                e.dataTransfer.effectAllowed = 'move';
                e.target.style.opacity = '0.5';
            });

            clockRow.addEventListener('dragend', (e) => {
                e.target.style.opacity = '1';
                const allRows = [...clockListContainer.querySelectorAll('div[draggable="true"]')];
                allRows.forEach(row => {
                    row.style.borderTop = '';
                    row.style.borderBottom = '';
                });
            });

            clockRow.addEventListener('dragover', (e) => {
                e.preventDefault();
                const allRows = [...clockListContainer.querySelectorAll('div[draggable="true"]')];
                allRows.forEach(row => {
                    row.style.borderTop = '';
                    row.style.borderBottom = '';
                });
                const rect = clockRow.getBoundingClientRect();
                const halfwayY = rect.top + rect.height / 2;
                if (e.clientY < halfwayY) {
                    clockRow.style.borderTop = '2px solid #ff8040';
                } else {
                    clockRow.style.borderBottom = '2px solid #ff8040';
                }
            });

            const clockName = document.createElement('span');
            clockName.textContent = clock.displayPlace || clock.timezone;
            clockRow.appendChild(clockName);

            const buttonsWrapper = document.createElement('div');

            const changeBtn = createTrackerButton('Change');
            changeBtn.dataset.clockId = clock.id;
            changeBtn.addEventListener('click', (e) => {
                activeClockSearchId = clock.id;
                const timezoneSearchContainer = document.getElementById('otk-timezone-search-container');
                if (timezoneSearchContainer) {
                    const buttonRect = e.target.getBoundingClientRect();
                    timezoneSearchContainer.style.top = `${buttonRect.bottom + 5}px`;
                    timezoneSearchContainer.style.left = `${buttonRect.left - timezoneSearchContainer.offsetWidth + buttonRect.width}px`;
                    timezoneSearchContainer.style.display = 'block';
                }
            });
            buttonsWrapper.appendChild(changeBtn);

            if (index > 0) { // Don't allow removing the first (primary) clock
                const removeBtn = createTrackerButton('Remove');
                removeBtn.dataset.clockId = clock.id;
                removeBtn.style.marginLeft = '5px';
                removeBtn.addEventListener('click', () => {
                    let currentClocks = JSON.parse(localStorage.getItem('otkClocks') || '[]');
                    currentClocks = currentClocks.filter(c => c.id !== clock.id);
                    localStorage.setItem('otkClocks', JSON.stringify(currentClocks));
                    renderClockOptions();
                    renderClocks();
                });
                buttonsWrapper.appendChild(removeBtn);
            }

            clockRow.appendChild(buttonsWrapper);
            clockListContainer.appendChild(clockRow);
        });

        clockListContainer.addEventListener('drop', (e) => {
            e.preventDefault();
            const targetRow = e.target.closest('div[draggable="true"]');
            if (!targetRow || draggedClockId === null) return;

            let currentClocks = JSON.parse(localStorage.getItem('otkClocks') || '[]');
            const draggedIndex = currentClocks.findIndex(c => c.id === draggedClockId);
            const targetIndex = currentClocks.findIndex(c => c.id === parseInt(targetRow.dataset.clockId));

            if (draggedIndex === -1 || targetIndex === -1) return;

            const rect = targetRow.getBoundingClientRect();
            const halfwayY = rect.top + rect.height / 2;
            const insertBefore = e.clientY < halfwayY;

            const [draggedClock] = currentClocks.splice(draggedIndex, 1);
            let newIndex;
            if (insertBefore) {
                newIndex = currentClocks.findIndex(c => c.id === parseInt(targetRow.dataset.clockId));
            } else {
                newIndex = currentClocks.findIndex(c => c.id === parseInt(targetRow.dataset.clockId)) + 1;
            }

            currentClocks.splice(newIndex, 0, draggedClock);

            localStorage.setItem('otkClocks', JSON.stringify(currentClocks));
            renderClockOptions();
            renderClocks();
            draggedClockId = null;
        });

        const footerWrapper = document.createElement('div');
        footerWrapper.style.cssText = `
            display: flex;
            justify-content: space-between;
            margin-top: 15px;
            gap: 10px;
        `;

        const addClockBtn = createTrackerButton('Add New Clock');
        addClockBtn.style.flex = '1';
        addClockBtn.addEventListener('click', () => {
            const currentClocks = JSON.parse(localStorage.getItem('otkClocks') || '[]');
            const newClock = {
                id: Date.now(),
                timezone: 'America/New_York',
                displayPlace: 'New York'
            };
            currentClocks.push(newClock);
            localStorage.setItem('otkClocks', JSON.stringify(currentClocks));
            renderClockOptions();
            renderClocks();
        });

        const closeBtn = createTrackerButton('Close');
        closeBtn.style.flex = '1';
        closeBtn.addEventListener('click', () => {
            document.getElementById('otk-clock-options-window').style.display = 'none';
        });

        const cogPositionWrapper = document.createElement('div');
        cogPositionWrapper.style.cssText = 'display: flex; justify-content: space-between; align-items: center; margin-top: 10px;';
        const cogPositionLabel = document.createElement('label');
        cogPositionLabel.textContent = 'Cog Position:';
        const cogPositionSelect = document.createElement('select');
        const options = ['Before Clocks', 'After Clocks'];
        options.forEach(opt => {
            const optionEl = document.createElement('option');
            optionEl.value = opt.toLowerCase().replace(' ', '-');
            optionEl.textContent = opt;
            cogPositionSelect.appendChild(optionEl);
        });
        cogPositionSelect.value = localStorage.getItem('otkClockCogPosition') || 'after-clocks';
        cogPositionSelect.addEventListener('change', () => {
            localStorage.setItem('otkClockCogPosition', cogPositionSelect.value);
            renderClocks();
        });
        cogPositionWrapper.appendChild(cogPositionLabel);
        cogPositionWrapper.appendChild(cogPositionSelect);

        footerWrapper.appendChild(addClockBtn);
        footerWrapper.appendChild(closeBtn);
        contentArea.appendChild(cogPositionWrapper);
        contentArea.appendChild(footerWrapper);
    }

    function renderClocks() {
        const clockContainer = document.getElementById('otk-clock');
        if (!clockContainer) return;

        clockContainer.innerHTML = ''; // Clear existing clocks
        const clocks = JSON.parse(localStorage.getItem('otkClocks') || '[]');

        clocks.forEach((clock, index) => {
            const clockInstance = document.createElement('div');
            clockInstance.className = 'otk-clock-instance';
            clockInstance.dataset.clockId = clock.id;
            clockInstance.style.display = 'flex';
            clockInstance.style.alignItems = 'center';
            clockInstance.style.padding = '0 5px';
            clockInstance.style.position = 'relative';

            const clockTextSpan = document.createElement('span');
            clockTextSpan.id = `otk-clock-text-${clock.id}`;
            clockInstance.appendChild(clockTextSpan);

            clockContainer.appendChild(clockInstance);

            if (index < clocks.length - 1) {
                const divider = document.createElement('span');
                divider.textContent = '|';
                divider.style.color = 'var(--otk-clock-divider-color, #ff8040)';
                divider.style.padding = '0 5px';
                clockContainer.appendChild(divider);
            }
        });

        const cogIcon = document.createElement('span');
        cogIcon.id = 'otk-clock-cog';
        cogIcon.innerHTML = '&#x2699;';
        cogIcon.style.cssText = 'font-size: 16px; margin: 0 10px; cursor: pointer; display: inline-block; color: var(--otk-clock-cog-color);';
        cogIcon.title = "Edit Clocks";
        cogIcon.addEventListener('click', () => {
            const clockOptionsWindow = document.getElementById('otk-clock-options-window');
            if (clockOptionsWindow) {
                const isHidden = clockOptionsWindow.style.display === 'none';
                clockOptionsWindow.style.display = isHidden ? 'flex' : 'none';
                if (isHidden) {
                    renderClockOptions();
                }
            }
        });

        const cogPosition = localStorage.getItem('otkClockCogPosition') || 'after-clocks';
        if (cogPosition === 'before-clocks') {
            clockContainer.insertBefore(cogIcon, clockContainer.firstChild);
        } else {
            clockContainer.appendChild(cogIcon);
        }

        updateClockTimes();
    }

    function updateClockTimes() {
        const clocks = JSON.parse(localStorage.getItem('otkClocks') || '[]');
        clocks.forEach(clock => {
            const clockTextElement = document.getElementById(`otk-clock-text-${clock.id}`);
            if (clockTextElement) {
                const timeZoneName = clock.displayPlace || clock.timezone.split('/').pop().replace(/_/g, ' ');
                const now = new Date();
                const timeString = now.toLocaleTimeString('en-US', {
                    timeZone: clock.timezone,
                    hour12: false,
                    hour: '2-digit',
                    minute: '2-digit',
                    second: '2-digit'
                });

                clockTextElement.innerHTML = ''; // Clear existing content
                const timeSpan = document.createElement('span');
                timeSpan.style.width = '65px'; // Fixed width to prevent "jiggle"
                timeSpan.style.display = 'inline-block'; // Needed for width to apply
                timeSpan.style.textAlign = 'center'; // Center the time within the fixed-width span
                timeSpan.textContent = timeString;

                const tzSpan = document.createElement('span');
                tzSpan.textContent = ` ${timeZoneName}`;

                clockTextElement.appendChild(timeSpan);
                clockTextElement.appendChild(tzSpan);
            }
        });
    }

function startAutoEmbedReloader() {
    setInterval(() => {
        if (!otkViewer || otkViewer.style.display === 'none') {
            return;
        }

        const iframes = otkViewer.querySelectorAll('iframe');
        iframes.forEach(iframe => {
            const hasDataSrc = iframe.dataset.src && iframe.dataset.src.trim() !== '';
            const hasSrc = iframe.src && iframe.src.trim() !== '' && iframe.src !== 'about:blank';

            if (hasDataSrc && !hasSrc) {
                consoleLog(`[AutoEmbedReloader] Found failed embed. Reloading src: ${iframe.dataset.src}`);
                iframe.src = iframe.dataset.src;
            }
        });
    }, 5000); // Check every 5 seconds
}





// --- IIFE Scope Helper for Intersection Observer ---
function handleIntersection(entries, observerInstance) {
    entries.forEach(entry => {
        const wrapper = entry.target;
        let iframe = wrapper.querySelector('iframe');

        if (entry.isIntersecting) {
            // Element is now visible
            if (!iframe) {
                // If the iframe was removed, recreate it
                const newIframe = document.createElement('iframe');
                // Copy attributes from a template or stored config if necessary
                // For now, assuming basic recreation is enough
                newIframe.style.position = 'absolute';
                newIframe.style.top = '0';
                newIframe.style.left = '0';
                newIframe.style.width = '100%';
                newIframe.style.height = '100%';
                newIframe.setAttribute('frameborder', '0');
                newIframe.setAttribute('allowfullscreen', 'true');
                if (wrapper.classList.contains('otk-twitch-embed-wrapper')) {
                    newIframe.setAttribute('scrolling', 'no');
                } else if (wrapper.classList.contains('otk-youtube-embed-wrapper')) {
                    newIframe.setAttribute('allow', 'accelerometer; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share');
                }
                newIframe.dataset.src = wrapper.dataset.embedUrl;
                wrapper.innerHTML = '';
    if (window.twttr?.widgets?.load) {
        twttr.widgets.load(wrapper);
    } // Clear placeholder
                wrapper.appendChild(newIframe);
                iframe = newIframe;
            }

            if (iframe && iframe.dataset.src && (!iframe.src || iframe.src === 'about:blank')) {
                consoleLog('[LazyLoad] Iframe is intersecting, loading src:', iframe.dataset.src);
                iframe.src = iframe.dataset.src;
            }
            observerInstance.unobserve(wrapper);
        } else {
            // Element is no longer visible
            if (wrapper.classList.contains('otk-tweet-embed-wrapper')) {
                return; // Do not unload tweet embeds
            }

            if (iframe && iframe.src && iframe.src !== 'about:blank') {
                consoleLog('[LazyLoad] Iframe is no longer intersecting, removing iframe for:', iframe.src);

                // For YouTube, try to pause the video before removing
                if (iframe.contentWindow && iframe.src.includes("youtube.com/embed")) {
                    try {
                        iframe.contentWindow.postMessage('{"event":"command","func":"pauseVideo","args":""}', 'https://www.youtube.com');
                    } catch (e) {
                        consoleWarn('[LazyLoad] Error attempting to postMessage pause to YouTube:', e);
                    }
                } else if (iframe.contentWindow && iframe.src.includes("twitch.tv")) {
                    try {
                        iframe.contentWindow.postMessage({"event": "video.pause"}, "*");
                    } catch (e) {
                        consoleWarn('[LazyLoad] Error attempting to postMessage pause to Twitch:', e);
                    }
                }

                // Store the embed URL on the wrapper if it's not already there
                if (!wrapper.dataset.embedUrl) {
                    wrapper.dataset.embedUrl = iframe.dataset.src;
                }

                // Remove the iframe and add a placeholder
                iframe.remove();
                const placeholder = document.createElement('div');
                placeholder.textContent = 'Embed hidden. Scroll to load.';
                placeholder.style.cssText = `
                    display: flex;
                    align-items: center;
                    justify-content: center;
                    width: 100%;
                    height: 100%;
                    background-color: #181818;
                    color: white;
                    font-size: 14px;
                `;
                wrapper.appendChild(placeholder);
                observerInstance.observe(wrapper);
            }
        }
    });
}

// --- Theme Settings Persistence ---
const THEME_SETTINGS_KEY = 'otkThemeSettings';
let pendingThemeChanges = {};

function showApplyDiscardButtons() {
    const applyBtn = document.getElementById('otk-apply-settings-btn');
    const discardBtn = document.getElementById('otk-discard-settings-btn');
    if (applyBtn) applyBtn.style.display = 'inline-block';
    if (discardBtn) discardBtn.style.display = 'inline-block';
}

function hideApplyDiscardButtons() {
    const applyBtn = document.getElementById('otk-apply-settings-btn');
    const discardBtn = document.getElementById('otk-discard-settings-btn');
    if (applyBtn) applyBtn.style.display = 'none';
    if (discardBtn) discardBtn.style.display = 'none';
}

async function forceViewerRerenderAfterThemeChange() {
    if (otkViewer && otkViewer.style.display === 'block') {
        consoleLog("Forcing viewer re-render after theme/setting change.");

        // Reload messages from DB to ensure we have the full set before applying limits
        messagesByThreadId = await loadMessagesFromDB();

        // No need to manually trim here, as renderMessagesInViewer will do it.
        // The key is that we've refreshed messagesByThreadId from the source of truth.

        // Clear viewer state
        renderedMessageIdsInViewer.clear();
        otkViewer.innerHTML = ''; // Clear the viewer content

        // Apply layout class
        const currentLayoutToggle = localStorage.getItem('otkMessageLayoutStyle') || 'default';
        if (currentLayoutToggle === 'new_design') {
            otkViewer.classList.add('otk-message-layout-newdesign');
            otkViewer.classList.remove('otk-message-layout-default');
        } else {
            otkViewer.classList.add('otk-message-layout-default');
            otkViewer.classList.remove('otk-message-layout-newdesign');
        }

        // Re-render, which will now use the freshly loaded and correctly trimmed messages
        renderMessagesInViewer({ isToggleOpen: true });
        consoleLog("Viewer force re-rendered with fresh data.");
    }
}

function saveThemeSetting(key, value, requiresRerender = false) {
    const threadListRerenderKeys = [
        'guiThreadListTitleColor',
        'guiThreadListTimeColor',
        'otkThreadTimePosition',
        'otkThreadTimeDividerEnabled',
        'otkThreadTimeDividerSymbol',
        'otkThreadTimeDividerColor',
        'otkThreadTimeBracketStyle',
        'otkThreadTimeBracketColor'
    ];

    if (requiresRerender) {
        pendingThemeChanges[key] = value;
        showApplyDiscardButtons();
    } else {
        let settings = {};
        try {
            settings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
        } catch (e) {
            consoleError("Error parsing theme settings from localStorage:", e);
        }
        if (value === null || value === undefined) {
            delete settings[key];
        } else {
            settings[key] = value;
        }
        localStorage.setItem(THEME_SETTINGS_KEY, JSON.stringify(settings));
        consoleLog("Saved theme setting:", key, value);
        if (key.startsWith('otkMsgDepth')) {
            forceViewerRerenderAfterThemeChange();
        }
        if (threadListRerenderKeys.includes(key)) {
            renderThreadList();
        }
    }
}

async function applyMainTheme() {
    // If theme settings already exist in localStorage, don't overwrite them with the main theme on page load.
    // This preserves user's session changes. Main theme is for initial load or after a reset.
    if (localStorage.getItem(THEME_SETTINGS_KEY)) {
        consoleLog('[Theme] Active theme settings found in localStorage. Skipping main theme load.');
        return;
    }

    try {
        const mainThemeSettings = await GM.getValue(MAIN_THEME_KEY);
        if (mainThemeSettings) {
            const parsedSettings = JSON.parse(mainThemeSettings);
            localStorage.setItem(THEME_SETTINGS_KEY, JSON.stringify(parsedSettings));
            consoleLog('[Theme] Loaded main theme from GM storage into localStorage.');
        } else {
            consoleLog('[Theme] No main theme found in GM storage. Using localStorage default.');
        }
    } catch (error) {
        consoleError('[Theme] Error loading main theme from GM storage:', error);
    }
}

function applyThemeSettings(options = {}) {
    const { forceRerender = true } = options; // Default to true to not break existing calls

    let settings = {};
    try {
        settings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
    } catch (e) {
        consoleError("Error parsing theme settings from localStorage:", e);
    }
    consoleLog("Applying theme settings:", settings);
    consoleLog("[Clock BG Debug] Applying theme. clockBgColor is:", settings.clockBgColor);

    // Helper to update a color input pair (hex text and color swatch)
        const updateColorInputs = (idSuffix, colorValue) => {
            const hexInput = document.getElementById(`otk-${idSuffix}-hex`);
            const pickerInput = document.getElementById(`otk-${idSuffix}`); // Correct ID for color swatch
            if (hexInput) hexInput.value = colorValue;
            if (pickerInput) pickerInput.value = colorValue;
        };

        if (settings.guiBgColor) {
            document.documentElement.style.setProperty('--otk-gui-bg-color', settings.guiBgColor);
            updateColorInputs('gui-bg', settings.guiBgColor);
        }

        if (settings.titleTextColor) {
            document.documentElement.style.setProperty('--otk-title-text-color', settings.titleTextColor);
            updateColorInputs('title-text', settings.titleTextColor);
        }

        if (settings.optionsTextColor) {
            document.documentElement.style.setProperty('--otk-options-text-color', settings.optionsTextColor);
            updateColorInputs('options-text', settings.optionsTextColor);
        }

        if (settings.actualStatsTextColor) {
            document.documentElement.style.setProperty('--otk-stats-text-color', settings.actualStatsTextColor);
            updateColorInputs('actual-stats-text', settings.actualStatsTextColor);
        }

        if (settings.viewerBgColor) {
            document.documentElement.style.setProperty('--otk-viewer-bg-color', settings.viewerBgColor);
            updateColorInputs('viewer-bg', settings.viewerBgColor);
        }

        if (settings.guiThreadListTitleColor) {
            document.documentElement.style.setProperty('--otk-gui-threadlist-title-color', settings.guiThreadListTitleColor);
            updateColorInputs('threadlist-title', settings.guiThreadListTitleColor);
        }

        if (settings.guiThreadListTimeColor) {
            document.documentElement.style.setProperty('--otk-gui-threadlist-time-color', settings.guiThreadListTimeColor);
            updateColorInputs('threadlist-time', settings.guiThreadListTimeColor);
        }

        // Viewer Header Border Color
        if (settings.viewerHeaderBorderColor) {
            document.documentElement.style.setProperty('--otk-viewer-header-border-color', settings.viewerHeaderBorderColor);
            updateColorInputs('viewer-header-border', settings.viewerHeaderBorderColor);
        }

        // Viewer Quote L1 Border Color
        if (settings.viewerQuote1HeaderBorderColor) {
            document.documentElement.style.setProperty('--otk-viewer-quote1-header-border-color', settings.viewerQuote1HeaderBorderColor);
            updateColorInputs('viewer-quote1-border', settings.viewerQuote1HeaderBorderColor);
        }

        // Viewer Quote L2+ Border Color
        if (settings.viewerQuote2plusHeaderBorderColor) {
            document.documentElement.style.setProperty('--otk-viewer-quote2plus-header-border-color', settings.viewerQuote2plusHeaderBorderColor);
            updateColorInputs('viewer-quote2plus-border', settings.viewerQuote2plusHeaderBorderColor);
        }

        // Message Background Colors, etc. for Even/Odd depths
        ['Even', 'Odd'].forEach(parity => {
            const parityLower = parity.toLowerCase();
            const settingsToApply = [
                { key: `msgDepth${parity}ContentFontSize`, cssVar: `--otk-msg-depth-${parityLower}-content-font-size`, idSuffix: `msg-depth-${parityLower}-content-fontsize`, type: 'font' },
                { key: `msgDepth${parity}BgColor`, cssVar: `--otk-msg-depth-${parityLower}-bg-color`, idSuffix: `msg-depth-${parityLower}-bg`, type: 'color' },
                { key: `msgDepth${parity}TextColor`, cssVar: `--otk-msg-depth-${parityLower}-text-color`, idSuffix: `msg-depth-${parityLower}-text`, type: 'color' },
                { key: `msgDepth${parity}HeaderTextColor`, cssVar: `--otk-msg-depth-${parityLower}-header-text-color`, idSuffix: `msg-depth-${parityLower}-header-text`, type: 'color' },
                { key: `viewerHeaderBorderColor${parity}`, cssVar: `--otk-viewer-header-border-color-${parityLower}`, idSuffix: `viewer-header-border-${parityLower}`, type: 'color' }
            ];

            settingsToApply.forEach(setting => {
                 if (settings[setting.key]) {
                    document.documentElement.style.setProperty(setting.cssVar, settings[setting.key]);
                    if (setting.type === 'color') {
                        updateColorInputs(setting.idSuffix, settings[setting.key]);
                    } else if (setting.type === 'font') {
                        const inputElement = document.getElementById(`otk-${setting.idSuffix}`);
                        if (inputElement) {
                            inputElement.value = settings[setting.key].replace('px', '');
                        }
                    }
                }
            });
        });


        if (settings.guiBottomBorderColor) {
            document.documentElement.style.setProperty('--otk-gui-bottom-border-color', settings.guiBottomBorderColor);
            updateColorInputs('gui-bottom-border', settings.guiBottomBorderColor);
        }

        // Cog Icon Color
        if (settings.cogIconColor) {
            document.documentElement.style.setProperty('--otk-cog-icon-color', settings.cogIconColor);
            updateColorInputs('cog-icon', settings.cogIconColor);
        }

        // Disable Background Font Color
        if (settings.disableBgFontColor) {
            document.documentElement.style.setProperty('--otk-disable-bg-font-color', settings.disableBgFontColor);
            updateColorInputs('disable-bg-font', settings.disableBgFontColor);
        }

        if (settings.countdownLabelTextColor) {
            document.documentElement.style.setProperty('--otk-countdown-label-text-color', settings.countdownLabelTextColor);
            updateColorInputs('countdown-label-text', settings.countdownLabelTextColor);
        }

        if (settings.countdownTimerTextColor) {
            document.documentElement.style.setProperty('--otk-countdown-timer-text-color', settings.countdownTimerTextColor);
            updateColorInputs('countdown-timer-text', settings.countdownTimerTextColor);
        }

        // New Messages Divider Color
        if (settings.newMessagesDividerColor) {
            document.documentElement.style.setProperty('--otk-new-messages-divider-color', settings.newMessagesDividerColor);
            updateColorInputs('new-msg-divider', settings.newMessagesDividerColor);
        }

        // New Messages Font Color
        if (settings.newMessagesFontColor) {
            document.documentElement.style.setProperty('--otk-new-messages-font-color', settings.newMessagesFontColor);
            updateColorInputs('new-msg-font', settings.newMessagesFontColor);
        }

        // Anchor Highlight Colors
        if (settings.anchorHighlightBgColor) {
            document.documentElement.style.setProperty('--otk-anchor-highlight-bg-color', settings.anchorHighlightBgColor);
            updateColorInputs('anchor-bg', settings.anchorHighlightBgColor);
        }
        if (settings.anchorHighlightBorderColor) {
            document.documentElement.style.setProperty('--otk-anchor-highlight-border-color', settings.anchorHighlightBorderColor);
            updateColorInputs('anchor-border', settings.anchorHighlightBorderColor);
        }

        // '+' Icon Background
        if (settings.plusIconBgColor) {
            document.documentElement.style.setProperty('--otk-plus-icon-bg-color', settings.plusIconBgColor);
            updateColorInputs('plus-icon-bg-color', settings.plusIconBgColor);
        }

        // Icon Colors
        if (settings.resizeIconColor) {
            document.documentElement.style.setProperty('--otk-resize-icon-color', settings.resizeIconColor);
            updateColorInputs('resize-icon', settings.resizeIconColor);
        }
        if (settings.resizeIconBgColor) {
            document.documentElement.style.setProperty('--otk-resize-icon-bg-color', settings.resizeIconBgColor);
            updateColorInputs('resize-icon-bg', settings.resizeIconBgColor);
        }
        if (settings.blurIconColor) {
            document.documentElement.style.setProperty('--otk-blur-icon-color', settings.blurIconColor);
            updateColorInputs('blur-icon', settings.blurIconColor);
        }
        if (settings.blurIconBgColor) {
            document.documentElement.style.setProperty('--otk-blur-icon-bg-color', settings.blurIconBgColor);
            updateColorInputs('blur-icon-bg', settings.blurIconBgColor);
        }

    // Clock Colors
        if (settings.hasOwnProperty('clockBgColor') && settings.clockBgColor) {
            document.documentElement.style.setProperty('--otk-clock-bg-color', settings.clockBgColor);
            updateColorInputs('clock-bg', settings.clockBgColor);
        } else {
            // If the setting is empty or doesn't exist, remove the inline style property.
            // This makes the element revert to the color defined in the <style> block's :root.
            document.documentElement.style.removeProperty('--otk-clock-bg-color');
            // Update the input to show the computed default color.
            const defaultColor = getComputedStyle(document.documentElement).getPropertyValue('--otk-clock-bg-color').trim();
            updateColorInputs('clock-bg', defaultColor);
        }
        if (settings.clockSearchBgColor) {
            document.documentElement.style.setProperty('--otk-clock-search-bg-color', settings.clockSearchBgColor);
            updateColorInputs('clock-search-bg', settings.clockSearchBgColor);
        }
        if (settings.clockSearchTextColor) {
            document.documentElement.style.setProperty('--otk-clock-search-text-color', settings.clockSearchTextColor);
            updateColorInputs('clock-search-text', settings.clockSearchTextColor);
        }
        if (settings.clockCogColor) {
            document.documentElement.style.setProperty('--otk-clock-cog-color', settings.clockCogColor);
            updateColorInputs('clock-cog', settings.clockCogColor);
        }

        // GUI Button Colors
        const buttonColorConfigs = [
            { key: 'guiButtonBgColor', cssVar: '--otk-button-bg-color', idSuffix: 'gui-button-bg' },
            { key: 'guiButtonTextColor', cssVar: '--otk-button-text-color', idSuffix: 'gui-button-text' },
            { key: 'guiButtonBorderColor', cssVar: '--otk-button-border-color', idSuffix: 'gui-button-border' },
            { key: 'guiButtonHoverBgColor', cssVar: '--otk-button-hover-bg-color', idSuffix: 'gui-button-hover-bg' },
            { key: 'guiButtonActiveBgColor', cssVar: '--otk-button-active-bg-color', idSuffix: 'gui-button-active-bg' }
        ];
        buttonColorConfigs.forEach(config => {
            if (settings[config.key]) {
                document.documentElement.style.setProperty(config.cssVar, settings[config.key]);
                updateColorInputs(config.idSuffix, settings[config.key]);
            }
        });

        // Loading Screen Colors
        if (settings.loadingOverlayBaseHexColor) {
            document.documentElement.style.setProperty('--otk-loading-overlay-base-hex-color', settings.loadingOverlayBaseHexColor);
            updateColorInputs('loading-overlay-base-hex', settings.loadingOverlayBaseHexColor);
        }
        if (settings.loadingOverlayOpacity) {
            document.documentElement.style.setProperty('--otk-loading-overlay-opacity', settings.loadingOverlayOpacity);
            const inputEl = document.getElementById('otk-loading-overlay-opacity');
            if (inputEl) inputEl.value = settings.loadingOverlayOpacity;
        }
        if (settings.loadingTextColor) {
            document.documentElement.style.setProperty('--otk-loading-text-color', settings.loadingTextColor);
            updateColorInputs('loading-text', settings.loadingTextColor);
        }
        if (settings.loadingProgressBarBgColor) {
            document.documentElement.style.setProperty('--otk-loading-progress-bar-bg-color', settings.loadingProgressBarBgColor);
            updateColorInputs('loading-progress-bg', settings.loadingProgressBarBgColor);
        }
        if (settings.loadingProgressBarFillColor) {
            document.documentElement.style.setProperty('--otk-loading-progress-bar-fill-color', settings.loadingProgressBarFillColor);
            updateColorInputs('loading-progress-fill', settings.loadingProgressBarFillColor);
        }
        if (settings.loadingProgressBarTextColor) {
            document.documentElement.style.setProperty('--otk-loading-progress-bar-text-color', settings.loadingProgressBarTextColor);
            updateColorInputs('loading-progress-text', settings.loadingProgressBarTextColor);
        }

        // Directly update loading screen styles
        const loadingOverlayElement = document.getElementById('otk-loading-overlay');
        if (loadingOverlayElement) {
            const baseHex = settings.loadingOverlayBaseHexColor || getComputedStyle(document.documentElement).getPropertyValue('--otk-loading-overlay-base-hex-color').trim() || '#000000';
            const rgbParts = hexToRgbParts(baseHex);
            const opacity = settings.loadingOverlayOpacity || getComputedStyle(document.documentElement).getPropertyValue('--otk-loading-overlay-opacity').trim() || '0.8';
            loadingOverlayElement.style.backgroundColor = `rgba(${rgbParts}, ${opacity})`;
            loadingOverlayElement.style.color = `var(--otk-loading-text-color, ${getComputedStyle(document.documentElement).getPropertyValue('--otk-loading-text-color').trim() || '#ffffff'})`;
            const progressBarContainer = document.getElementById('otk-progress-bar-container');
            if (progressBarContainer) {
                progressBarContainer.style.backgroundColor = `var(--otk-loading-progress-bar-bg-color, ${getComputedStyle(document.documentElement).getPropertyValue('--otk-loading-progress-bar-bg-color').trim() || '#333333'})`;
            }
            const progressBar = document.getElementById('otk-progress-bar');
            if (progressBar) {
                progressBar.style.backgroundColor = `var(--otk-loading-progress-bar-fill-color, ${getComputedStyle(document.documentElement).getPropertyValue('--otk-loading-progress-bar-fill-color').trim() || '#4CAF50'})`;
                progressBar.style.color = `var(--otk-loading-progress-bar-text-color, ${getComputedStyle(document.documentElement).getPropertyValue('--otk-loading-progress-bar-text-color').trim() || '#ffffff'})`;
            }
        }

        // GUI Background Image
        const guiWrapper = document.getElementById('otk-tracker-gui-wrapper');
        if (guiWrapper) {
            if (settings.guiBackgroundImageUrl) {
                guiWrapper.style.backgroundImage = `url('${settings.guiBackgroundImageUrl}')`;
                guiWrapper.style.backgroundSize = settings.guiBgSize || 'cover';
                guiWrapper.style.backgroundRepeat = settings.guiBgRepeat || 'no-repeat';
                guiWrapper.style.backgroundPosition = settings.guiBgPosition || 'center';
            } else {
                guiWrapper.style.backgroundImage = '';
            }
        }

        if (forceRerender) {
            forceViewerRerenderAfterThemeChange();
        }

        // Viewer Background Image
        const viewerWrapper = document.getElementById('otk-viewer');
        if (viewerWrapper) {
            if (settings.viewerBackgroundImageUrl) {
                viewerWrapper.style.backgroundImage = `url('${settings.viewerBackgroundImageUrl}')`;
                viewerWrapper.style.backgroundSize = settings.viewerBgSize || 'cover';
                viewerWrapper.style.backgroundRepeat = settings.viewerBgRepeat || 'no-repeat';
                viewerWrapper.style.backgroundPosition = settings.viewerBgPosition || 'center';
            } else {
                viewerWrapper.style.backgroundImage = '';
            }
        }

        // GUI Thread Box Outline
        if (settings.guiThreadBoxOutlineColor && settings.guiThreadBoxOutlineColor.toLowerCase() !== 'none') {
            document.documentElement.style.setProperty('--otk-gui-thread-box-outline', `1px solid ${settings.guiThreadBoxOutlineColor}`);
        } else {
            document.documentElement.style.setProperty('--otk-gui-thread-box-outline', 'none');
        }

        // Viewer Thread Box Outline
        if (settings.viewerThreadBoxOutlineColor && settings.viewerThreadBoxOutlineColor.toLowerCase() !== 'none') {
            document.documentElement.style.setProperty('--otk-viewer-thread-box-outline', `1px solid ${settings.viewerThreadBoxOutlineColor}`);
        } else {
            document.documentElement.style.setProperty('--otk-viewer-thread-box-outline', 'none');
        }

        // PiP Background
        applyPipBackgroundStyles(); // New centralized function
        if (settings.pipBackgroundColor) {
            document.documentElement.style.setProperty('--otk-pip-bg-color', settings.pipBackgroundColor);
            updateColorInputs('pip-bg', settings.pipBackgroundColor);
        }
    }


    function createColorOrNoneOptionRow(options) {
        // options = { labelText, storageKey, defaultValue, idSuffix }
        const group = document.createElement('div');
        group.style.cssText = `
            display: flex;
            align-items: center;
            gap: 8px;
            width: 100%;
            margin-bottom: 5px;
        `;

        const label = document.createElement('label');
        label.textContent = options.labelText;
        label.htmlFor = `otk-${options.idSuffix}-text`;
        label.style.cssText = `
            font-size: 12px;
            text-align: left;
            flex-basis: 230px;
            flex-shrink: 0;
        `;

        const controlsWrapperDiv = document.createElement('div');
        controlsWrapperDiv.style.cssText = `
            display: flex;
            flex-grow: 1;
            align-items: center;
            gap: 8px;
            min-width: 0;
        `;

        const textInput = document.createElement('input');
        textInput.type = 'text';
        textInput.id = `otk-${options.idSuffix}-text`;
        textInput.style.cssText = `
            flex: 1 1 70px;
            min-width: 50px;
            height: 25px;
            box-sizing: border-box;
            font-size: 12px;
            text-align: right;
        `;

        const colorPicker = document.createElement('input');
        colorPicker.type = 'color';
        colorPicker.id = `otk-${options.idSuffix}-picker`;
        colorPicker.style.cssText = `
            flex-grow: 0;
            flex-shrink: 0;
            width: 30px;
            height: 25px;
            padding: 1px;
            box-sizing: border-box;
        `;

        const defaultBtn = document.createElement('button');
        defaultBtn.textContent = 'Default';
        defaultBtn.style.cssText = `
            flex-grow: 0;
            flex-shrink: 0;
            padding: 2px 6px;
            height: 25px;
            font-size: 11px;
            box-sizing: border-box;
            width: auto;
        `;

        group.appendChild(label);
        controlsWrapperDiv.appendChild(textInput);
        controlsWrapperDiv.appendChild(colorPicker);
        controlsWrapperDiv.appendChild(defaultBtn);
        group.appendChild(controlsWrapperDiv);

        // Logic
        const settings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
        let initialValue = settings[options.storageKey] || options.defaultValue;
        textInput.value = initialValue;

        const isValidColor = (str) => /^#([0-9A-F]{3}){1,2}$/i.test(str);

        if (isValidColor(initialValue)) {
            colorPicker.value = initialValue;
        } else {
            colorPicker.value = '#000000'; // Default picker to black if value is "none"
        }
        colorPicker.style.visibility = 'visible'; // Always visible

        const updateState = (newValue) => {
            const valueToSave = newValue.trim().toLowerCase();
            textInput.value = valueToSave;
            if (isValidColor(valueToSave)) {
                colorPicker.value = valueToSave;
            }
            // No need to toggle visibility anymore
            saveThemeSetting(options.storageKey, valueToSave);
            applyThemeSettings({ forceRerender: false });
        };

        textInput.addEventListener('change', (e) => {
            const value = e.target.value.trim().toLowerCase();
            if (value === 'none' || isValidColor(value)) {
                updateState(value);
            } else {
                const savedSettings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
                textInput.value = savedSettings[options.storageKey] || options.defaultValue;
            }
        });

        colorPicker.addEventListener('input', (e) => {
            updateState(e.target.value);
        });

        defaultBtn.addEventListener('click', () => {
            updateState(options.defaultValue);
        });

        return group;
    }


    function applyPipBackgroundStyles() {
        const pipBackground = document.getElementById('otk-pip-background');
        if (!pipBackground) return;

        const settings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
        pipBackground.style.backgroundColor = settings.pipBackgroundColor || '#1a1a1a';
        if (settings.pipBackgroundImageUrl) {
            pipBackground.style.backgroundImage = `url('${settings.pipBackgroundImageUrl}')`;
            pipBackground.style.backgroundSize = settings.pipBgSize || 'cover';
            pipBackground.style.backgroundRepeat = settings.pipBgRepeat || 'no-repeat';
            pipBackground.style.backgroundPosition = settings.pipBgPosition || 'center';
        } else {
            pipBackground.style.backgroundImage = '';
        }
    }

    function createPipResizer() {
        let resizeHandle = document.getElementById('otk-resize-handle');
        if (resizeHandle) return; // Already exists

        resizeHandle = document.createElement('div');
        resizeHandle.id = 'otk-resize-handle';
        document.body.appendChild(resizeHandle);

        let isResizing = false;
        const viewer = document.getElementById('otk-viewer');
        const pipBackground = document.getElementById('otk-pip-background');

        const onMouseDown = (e) => {
            isResizing = true;
            document.body.classList.add('otk-resizing');
        };

        let latestX = 0;
        let isRafPending = false;

        const updateWidth = () => {
            if (!viewer) return; // Guard against viewer being null
            const newWidth = Math.max(200, Math.min(latestX, window.innerWidth - 200));
            viewer.style.width = newWidth + 'px';
            resizeHandle.style.left = newWidth + 'px';
            if (pipBackground) {
                pipBackground.style.left = newWidth + 'px';
                pipBackground.style.width = (window.innerWidth - newWidth) + 'px';
            }
            isRafPending = false;
        };

        const onMouseMove = (e) => {
            if (!isResizing) return;
            latestX = e.clientX;
            if (!isRafPending) {
                isRafPending = true;
                requestAnimationFrame(updateWidth);
            }
        };

        const onMouseUp = () => {
            isResizing = false;
            document.body.classList.remove('otk-resizing');
        };

        resizeHandle.addEventListener('mousedown', onMouseDown);
        document.addEventListener('mousemove', onMouseMove);
        document.addEventListener('mouseup', onMouseUp);

        // Store listeners so they can be removed
        resizeHandle.otkListeners = { onMouseDown, onMouseMove, onMouseUp };
    }

    function destroyPipResizer() {
        const resizeHandle = document.getElementById('otk-resize-handle');
        if (resizeHandle && resizeHandle.otkListeners) {
            const { onMouseDown, onMouseMove, onMouseUp } = resizeHandle.otkListeners;
            resizeHandle.removeEventListener('mousedown', onMouseDown);
            document.removeEventListener('mousemove', onMouseMove);
            document.removeEventListener('mouseup', onMouseUp);
            resizeHandle.remove();
        }
    }

    function enablePipMode() {
        const viewer = document.getElementById('otk-viewer');
        if (!viewer) return;

        viewer.style.width = '50vw';
        viewer.style.right = 'auto';

        let pipBackground = document.getElementById('otk-pip-background');
        if (!pipBackground) {
            pipBackground = document.createElement('div');
            pipBackground.id = 'otk-pip-background';
            pipBackground.style.position = 'fixed';
            pipBackground.style.top = '86px';
            pipBackground.style.left = '50vw';
            pipBackground.style.width = '50vw';
            pipBackground.style.height = 'calc(100% - 86px)';
            pipBackground.style.zIndex = '9997';
            document.body.appendChild(pipBackground);
        }

        applyPipBackgroundStyles();
        createPipResizer();
    }

    function disablePipMode() {
        const viewer = document.getElementById('otk-viewer');
        if (viewer) {
            viewer.style.width = '100vw';
            viewer.style.right = '0';
        }

        const pipBackground = document.getElementById('otk-pip-background');
        if (pipBackground) {
            pipBackground.remove();
        }

        destroyPipResizer();
    }

    function setupOptionsWindow() {
        consoleLog("Setting up Options Window...");

        // Check if window already exists
        if (document.getElementById('otk-options-window')) {
            consoleLog("Options window already exists.");
            return;
        }

        const optionsWindow = document.createElement('div');
        optionsWindow.id = 'otk-options-window';
        optionsWindow.style.cssText = `
            position: fixed;
            top: 100px;
            left: 100px;
            width: 545px; /* Further Increased width for scrollbar clearance (540px + 5px) */
            min-height: 150px; /* Minimum height when collapsed */
            max-height: 550px; /* Maximum height when expanded (title + theme heading + theme options container max-height + paddings) */
            background-color: #2c2c2c; /* Slightly lighter than GUI for distinction */
            border: 1px solid #444;
            border-radius: 5px;
            z-index: 10000; /* Below loading screen, above viewer/GUI */
            display: none; /* Hidden by default */
            flex-direction: column;
            box-shadow: 0 5px 15px rgba(0,0,0,0.5);
            color: var(--otk-options-text-color); /* Use specific variable for options window text */
        `;

        const titleBar = document.createElement('div');
        titleBar.id = 'otk-options-title-bar';
        titleBar.style.cssText = `
            padding: 8px 12px;
            background-color: #383838;
            color: #f0f0f0;
            font-weight: bold;
            cursor: move; /* For dragging */
            border-bottom: 1px solid #444;
            border-top-left-radius: 5px;
            border-top-right-radius: 5px;
            display: flex;
            justify-content: space-between;
            align-items: center;
        `;
        titleBar.textContent = 'Options'; // Changed title

        const titleBarButtons = document.createElement('div');
        titleBarButtons.style.display = 'flex';
        titleBarButtons.style.alignItems = 'center';

        const applyButton = createTrackerButton('Apply', 'otk-apply-settings-btn');
        applyButton.style.display = 'none'; // Hidden by default
        applyButton.style.marginRight = '10px';
        titleBarButtons.appendChild(applyButton);

        const discardButton = createTrackerButton('Discard', 'otk-discard-settings-btn');
        discardButton.style.display = 'none'; // Hidden by default
        discardButton.style.marginRight = '10px';
        discardButton.style.backgroundColor = '#803333';
        discardButton.onmouseover = () => discardButton.style.backgroundColor = '#a04444';
        discardButton.onmouseout = () => discardButton.style.backgroundColor = '#803333';
        titleBarButtons.appendChild(discardButton);

        const closeButton = document.createElement('span');
        closeButton.id = 'otk-options-close-btn';
        closeButton.innerHTML = '&#x2715;'; // 'X' character
        closeButton.style.cssText = `
            cursor: pointer;
            font-size: 16px;
            padding: 0 5px;
        `;
        closeButton.title = "Close Settings";
        titleBarButtons.appendChild(closeButton);

        titleBar.appendChild(titleBarButtons);
        optionsWindow.appendChild(titleBar);

        applyButton.addEventListener('click', () => {
            let settings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
            settings = { ...settings, ...pendingThemeChanges };
            localStorage.setItem(THEME_SETTINGS_KEY, JSON.stringify(settings));
            pendingThemeChanges = {};
            hideApplyDiscardButtons();
            applyThemeSettings();
        });

        discardButton.addEventListener('click', () => {
            pendingThemeChanges = {};
            hideApplyDiscardButtons();
            applyThemeSettings(); // Re-apply original settings to reset inputs
        });

        const contentArea = document.createElement('div');
        contentArea.id = 'otk-options-content';
        contentArea.style.cssText = `
            padding: 15px 10px 15px 20px; /* Top, Right (10px), Bottom, Left (20px) */
            flex-grow: 1; /* Allows content to fill space */
            overflow-y: auto; /* If content gets too long */
            box-sizing: border-box; /* Ensure padding is included in width/height */
            /* display: flex; Will be handled by section container */
            /* flex-direction: column; */
            /* gap: 10px; */
        `;
        optionsWindow.appendChild(contentArea);

        // --- Main Sections Container (for tabs or collapsible sections later) ---
        // This container might not be strictly necessary anymore if we are just stacking sections.
        // For now, let's keep it but add general settings directly to contentArea or sectionsContainer.
        // Let's add general settings directly to contentArea, above the theme section.

        const generalSettingsSection = document.createElement('div');
        generalSettingsSection.id = 'otk-general-settings-section';
        generalSettingsSection.style.cssText = `
            display: flex;
            flex-direction: column;
            gap: 10px; /* Space between general option groups */
            margin-bottom: 15px; /* Space before the theme section */
            padding-right: 5px; /* Added right padding */
            box-sizing: border-box; /* Ensure padding is included if not already part of a width calc */
        `;
        contentArea.appendChild(generalSettingsSection); // Add general settings section first

        // Add a heading for the General Settings section using the helper
        generalSettingsSection.appendChild(createSectionHeading('General Settings'));

        // --- Tracked Keyword(s) Option ---
        const trackedKeywordsGroup = document.createElement('div');
        // Apply Flexbox styling similar to createThemeOptionRow
        trackedKeywordsGroup.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const trackedKeywordsLabel = document.createElement('label');
        trackedKeywordsLabel.textContent = "Tracked Keyword(s):";
        trackedKeywordsLabel.htmlFor = 'otk-tracked-keywords-input';
        // Apply Flexbox label styling
        trackedKeywordsLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const trackedKeywordsControlsWrapper = document.createElement('div');
        trackedKeywordsControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0;";

        const trackedKeywordsInput = document.createElement('input');
        trackedKeywordsInput.type = 'text';
        trackedKeywordsInput.id = 'otk-tracked-keywords-input';
        trackedKeywordsInput.placeholder = "e.g., otk, item2, phrase three";
        // Explicitly set width to 100% of its parent wrapper and right-align text.
        trackedKeywordsInput.style.cssText = "width: 100%; height: 25px; box-sizing: border-box; font-size: 12px; text-align: right;";
        trackedKeywordsInput.value = localStorage.getItem(OTK_TRACKED_KEYWORDS_KEY) || "otk"; // Load saved value or default

        trackedKeywordsInput.addEventListener('change', () => { // Save on change (after blur or Enter)
            const valueToSave = trackedKeywordsInput.value.trim();
            if (valueToSave) {
                localStorage.setItem(OTK_TRACKED_KEYWORDS_KEY, valueToSave);
                consoleLog(`Tracked keywords saved: ${valueToSave}`);
            } else { // If input is cleared, revert to default and save that
                localStorage.setItem(OTK_TRACKED_KEYWORDS_KEY, "otk");
                trackedKeywordsInput.value = "otk"; // Reflect default in input
                consoleLog(`Tracked keywords reset to default: "otk"`);
            }
        });

        trackedKeywordsControlsWrapper.appendChild(trackedKeywordsInput);
        trackedKeywordsGroup.appendChild(trackedKeywordsLabel);
        trackedKeywordsGroup.appendChild(trackedKeywordsControlsWrapper);
        generalSettingsSection.appendChild(trackedKeywordsGroup);

        // --- Background Update Frequency Option ---
        const minUpdateGroup = createThemeOptionRow({
            labelText: "Minimum time between updates (minutes):",
            storageKey: 'otkMinUpdateSeconds',
            cssVariable: '--otk-min-update-seconds',
            defaultValue: '2',
            inputType: 'number',
            unit: null,
            min: 2,
            max: 60,
            idSuffix: 'min-update-seconds'
        });
        generalSettingsSection.appendChild(minUpdateGroup);

        const maxUpdateGroup = createThemeOptionRow({
            labelText: "Maximum time between updates (minutes):",
            storageKey: 'otkMaxUpdateSeconds',
            cssVariable: '--otk-max-update-seconds',
            defaultValue: '5',
            inputType: 'number',
            unit: null,
            min: 4,
            max: 60,
            idSuffix: 'max-update-seconds'
        });
        generalSettingsSection.appendChild(maxUpdateGroup);

        // --- Suspend After Inactive Option ---
        const suspendGroup = document.createElement('div');
        suspendGroup.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const suspendLabel = document.createElement('label');
        suspendLabel.textContent = "Suspend after inactivity:";
        suspendLabel.htmlFor = 'otk-suspend-after-inactive-select';
        suspendLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const suspendControlsWrapper = document.createElement('div');
        suspendControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0;";

        const suspendSelect = document.createElement('select');
        suspendSelect.id = 'otk-suspend-after-inactive-select';
        suspendSelect.style.cssText = "width: 100%; height: 25px; box-sizing: border-box; font-size: 12px;";

        const suspendOptions = ["Disabled", "1", "5", "10", "15", "30", "60"];
        suspendOptions.forEach(opt => {
            const optionElement = document.createElement('option');
            optionElement.value = opt;
            optionElement.textContent = opt;
            suspendSelect.appendChild(optionElement);
        });

        suspendSelect.value = localStorage.getItem('otkSuspendAfterInactiveMinutes') || '1';

        suspendSelect.addEventListener('change', () => {
            localStorage.setItem('otkSuspendAfterInactiveMinutes', suspendSelect.value);
            consoleLog(`Suspend after inactive time saved: ${suspendSelect.value}`);
        });

        suspendControlsWrapper.appendChild(suspendSelect);
        suspendGroup.appendChild(suspendLabel);
        suspendGroup.appendChild(suspendControlsWrapper);
        generalSettingsSection.appendChild(suspendGroup);

        // --- Media Load Mode Option ---
        const mediaLoadModeGroup = document.createElement('div');
        mediaLoadModeGroup.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const mediaLoadModeLabel = document.createElement('label');
        mediaLoadModeLabel.textContent = "Attached Media Load Mode:";
        mediaLoadModeLabel.htmlFor = 'otk-media-load-mode-select';
        mediaLoadModeLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const mediaLoadModeControlsWrapper = document.createElement('div');
        mediaLoadModeControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0;";

        const mediaLoadModeSelect = document.createElement('select');
        mediaLoadModeSelect.id = 'otk-media-load-mode-select';
        mediaLoadModeSelect.style.cssText = "width: 100%; height: 25px; box-sizing: border-box; font-size: 12px;";

        const mediaLoadOptions = [
            { label: 'Source First (Default)', value: 'source_first' },
            { label: 'Cache Only', value: 'cache_only' }
        ];

        mediaLoadOptions.forEach(opt => {
            const optionElement = document.createElement('option');
            optionElement.value = opt.value;
            optionElement.textContent = opt.label;
            mediaLoadModeSelect.appendChild(optionElement);
        });

        mediaLoadModeSelect.value = localStorage.getItem('otkMediaLoadMode') || 'source_first';

        mediaLoadModeSelect.addEventListener('change', () => {
            localStorage.setItem('otkMediaLoadMode', mediaLoadModeSelect.value);
            consoleLog(`Media load mode saved: ${mediaLoadModeSelect.value}`);
            alert('Media loading preference saved. This will take effect for newly rendered messages.');
        });

        mediaLoadModeControlsWrapper.appendChild(mediaLoadModeSelect);
        mediaLoadModeGroup.appendChild(mediaLoadModeLabel);
        mediaLoadModeGroup.appendChild(mediaLoadModeControlsWrapper);
        generalSettingsSection.appendChild(mediaLoadModeGroup);


        // --- Debugging Toggle Option ---
        const debugToggleGroup = document.createElement('div');
        // Apply Flexbox styling
        debugToggleGroup.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const debugToggleLabel = document.createElement('label');
        debugToggleLabel.textContent = "Enable Console Debugging:";
        debugToggleLabel.htmlFor = 'otk-debug-mode-checkbox';
        // Apply Flexbox label styling
        debugToggleLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const debugToggleControlsWrapper = document.createElement('div');
        debugToggleControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0; justify-content: flex-end;";

        const debugToggleCheckbox = document.createElement('input');
        debugToggleCheckbox.type = 'checkbox';
        debugToggleCheckbox.id = 'otk-debug-mode-checkbox';
        // Specific styling for checkbox
        debugToggleCheckbox.style.cssText = "height: 16px; width: 16px;";
        debugToggleCheckbox.checked = DEBUG_MODE;

        debugToggleCheckbox.addEventListener('change', () => {
            DEBUG_MODE = debugToggleCheckbox.checked;
            localStorage.setItem(DEBUG_MODE_KEY, DEBUG_MODE.toString());
            consoleLog(`Debug mode ${DEBUG_MODE ? 'enabled' : 'disabled'}.`);
            if (DEBUG_MODE) {
                 consoleLog('[OTK Tracker]', `Debug mode explicitly enabled via UI.`);
            }
        });

        debugToggleControlsWrapper.appendChild(debugToggleCheckbox);
        debugToggleGroup.appendChild(debugToggleLabel);
        debugToggleGroup.appendChild(debugToggleControlsWrapper);
        generalSettingsSection.appendChild(debugToggleGroup);

        // --- Memory Usage Report ---
        const memoryReportGroup = document.createElement('div');
        memoryReportGroup.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const memoryReportLabel = document.createElement('label');
        memoryReportLabel.textContent = "Enable Memory Usage Report:";
        memoryReportLabel.htmlFor = 'otk-memory-report-checkbox';
        memoryReportLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const memoryReportControlsWrapper = document.createElement('div');
        memoryReportControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0; justify-content: flex-end;";

        const memoryReportCheckbox = document.createElement('input');
        memoryReportCheckbox.type = 'checkbox';
        memoryReportCheckbox.id = 'otk-memory-report-checkbox';
        memoryReportCheckbox.style.cssText = "height: 16px; width: 16px;";
        memoryReportCheckbox.checked = localStorage.getItem('otkMemoryReportEnabled') === 'true';

        memoryReportCheckbox.addEventListener('change', () => {
            const isEnabled = memoryReportCheckbox.checked;
            localStorage.setItem('otkMemoryReportEnabled', isEnabled);
            const memoryReportButton = document.getElementById('otk-memory-report-btn');
            if (memoryReportButton) {
                memoryReportButton.style.display = isEnabled ? 'inline-block' : 'none';
            }
        });

        memoryReportControlsWrapper.appendChild(memoryReportCheckbox);
        memoryReportGroup.appendChild(memoryReportLabel);
        memoryReportGroup.appendChild(memoryReportControlsWrapper);
        generalSettingsSection.appendChild(memoryReportGroup);

        // --- Disable Background Updates Option ---
        const bgUpdateGroup = document.createElement('div');
        bgUpdateGroup.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const bgUpdateLabel = document.createElement('label');
        bgUpdateLabel.textContent = "Disable Background Updates:";
        bgUpdateLabel.htmlFor = 'otk-disable-bg-update-checkbox';
        bgUpdateLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const bgUpdateControlsWrapper = document.createElement('div');
        bgUpdateControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0; justify-content: flex-end;";

        const bgUpdateCheckbox = document.createElement('input');
        bgUpdateCheckbox.type = 'checkbox';
        bgUpdateCheckbox.id = 'otk-disable-bg-update-checkbox';
        bgUpdateCheckbox.style.cssText = "height: 16px; width: 16px;";
        bgUpdateCheckbox.checked = localStorage.getItem(BACKGROUND_UPDATES_DISABLED_KEY) === 'true';

        bgUpdateCheckbox.addEventListener('change', () => {
            if (bgUpdateCheckbox.checked) {
                stopBackgroundRefresh();
                if (countdownIntervalId) {
                    clearInterval(countdownIntervalId);
                    countdownIntervalId = null;
                }
                const countdownTimer = document.getElementById('otk-countdown-timer');
                if (countdownTimer) {
                    countdownTimer.textContent = 'n/a';
                }
                localStorage.setItem(BACKGROUND_UPDATES_DISABLED_KEY, 'true');
                consoleLog('Background updates disabled via checkbox.');
            } else {
                localStorage.setItem(BACKGROUND_UPDATES_DISABLED_KEY, 'false');
                startBackgroundRefresh(true); // Start immediately
                consoleLog('Background updates enabled via checkbox.');
            }
        });

        bgUpdateControlsWrapper.appendChild(bgUpdateCheckbox);
        bgUpdateGroup.appendChild(bgUpdateLabel);
        bgUpdateGroup.appendChild(bgUpdateControlsWrapper);
        generalSettingsSection.appendChild(bgUpdateGroup);

        // --- Clock Toggle Option ---
        const clockToggleGroup = document.createElement('div');
        clockToggleGroup.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const clockToggleLabel = document.createElement('label');
        clockToggleLabel.textContent = "Enable Clock:";
        clockToggleLabel.htmlFor = 'otk-clock-toggle-checkbox';
        clockToggleLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const clockToggleControlsWrapper = document.createElement('div');
        clockToggleControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0; justify-content: flex-end;";

        const clockToggleCheckbox = document.createElement('input');
        clockToggleCheckbox.type = 'checkbox';
        clockToggleCheckbox.id = 'otk-clock-toggle-checkbox';
        clockToggleCheckbox.style.cssText = "height: 16px; width: 16px;";
        clockToggleCheckbox.checked = localStorage.getItem('otkClockEnabled') === 'true';

        clockToggleCheckbox.addEventListener('change', () => {
            const isEnabled = clockToggleCheckbox.checked;
            localStorage.setItem('otkClockEnabled', isEnabled);
            const clockElement = document.getElementById('otk-clock');
            if (clockElement) {
                clockElement.style.display = isEnabled ? 'block' : 'none';
            }
        });

        clockToggleControlsWrapper.appendChild(clockToggleCheckbox);
        clockToggleGroup.appendChild(clockToggleLabel);
        clockToggleGroup.appendChild(clockToggleControlsWrapper);
        generalSettingsSection.appendChild(clockToggleGroup);

        // --- Message Limiting Feature ---
        const messageLimitGroup = document.createElement('div');
        messageLimitGroup.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const messageLimitLabel = document.createElement('label');
        messageLimitLabel.textContent = "Limit Number of Messages:";
        messageLimitLabel.htmlFor = 'otk-message-limit-checkbox';
        messageLimitLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const messageLimitControlsWrapper = document.createElement('div');
        messageLimitControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0; justify-content: flex-end;";

        const messageLimitCheckbox = document.createElement('input');
        messageLimitCheckbox.type = 'checkbox';
        messageLimitCheckbox.id = 'otk-message-limit-checkbox';
        messageLimitCheckbox.style.cssText = "height: 16px; width: 16px;";
        const initialThemeSettings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
        messageLimitCheckbox.checked = initialThemeSettings.otkMessageLimitEnabled !== false;

        const messageLimitInput = document.createElement('input');
        messageLimitInput.type = 'number';
        messageLimitInput.id = 'otk-message-limit-input';
        messageLimitInput.min = '1';
        messageLimitInput.style.cssText = "width: 70px; height: 25px; box-sizing: border-box; font-size: 12px; text-align: right;";
        messageLimitInput.value = initialThemeSettings.otkMessageLimitValue || '500';
        messageLimitInput.disabled = !messageLimitCheckbox.checked;

        messageLimitCheckbox.addEventListener('change', () => {
            const isEnabled = messageLimitCheckbox.checked;
            saveThemeSetting('otkMessageLimitEnabled', isEnabled, true);
            messageLimitInput.disabled = !isEnabled;
        });

        messageLimitInput.addEventListener('change', () => {
            saveThemeSetting('otkMessageLimitValue', messageLimitInput.value, true);
        });

        messageLimitControlsWrapper.appendChild(messageLimitCheckbox);
        messageLimitControlsWrapper.appendChild(messageLimitInput);
        messageLimitGroup.appendChild(messageLimitLabel);
        messageLimitGroup.appendChild(messageLimitControlsWrapper);
        generalSettingsSection.appendChild(messageLimitGroup);

        // --- Picture-in-Picture Toggle Option ---
        const pipToggleGroup = document.createElement('div');
        pipToggleGroup.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const pipToggleLabel = document.createElement('label');
        pipToggleLabel.textContent = "Enable Picture-in-Picture Mode:";
        pipToggleLabel.htmlFor = 'otk-pip-mode-checkbox';
        pipToggleLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const pipToggleControlsWrapper = document.createElement('div');
        pipToggleControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0; justify-content: flex-end;";

        const pipToggleCheckbox = document.createElement('input');
        pipToggleCheckbox.type = 'checkbox';
        pipToggleCheckbox.id = 'otk-pip-mode-checkbox';
        pipToggleCheckbox.style.cssText = "height: 16px; width: 16px;";
        pipToggleCheckbox.checked = localStorage.getItem('otkPipModeEnabled') === 'true';

        pipToggleCheckbox.addEventListener('change', () => {
            const isEnabled = pipToggleCheckbox.checked;
            localStorage.setItem('otkPipModeEnabled', isEnabled);
            const pipButton = document.getElementById('otk-pip-btn');
            if (pipButton) {
                pipButton.style.display = isEnabled ? 'inline-block' : 'none';
            }
        });

        pipToggleControlsWrapper.appendChild(pipToggleCheckbox);
        pipToggleGroup.appendChild(pipToggleLabel);
        pipToggleGroup.appendChild(pipToggleControlsWrapper);
        generalSettingsSection.appendChild(pipToggleGroup);


        // --- Theme/Appearance Section ---
        // This section will now be added after the general settings.
        // The 'sectionsContainer' might be redundant if themeSection is the only thing in it.
        // Let's append themeSection directly to contentArea as well, after generalSettingsSection.
        const sectionsContainer = document.createElement('div'); // Keep for potential future use if more sections are added here
        contentArea.appendChild(sectionsContainer);


        const themeSection = document.createElement('div');
        themeSection.id = 'otk-options-theme-section';
        themeSection.style.cssText = `
            display: flex;
            flex-direction: column;
            gap: 10px; /* Space between color option groups */
            /* max-height: 330px; */ /* Max height for the theme options area - Let content dictate or use min-height */
            /* overflow-y: auto; */ /* Enable vertical scrollbar - Let themeOptionsContainer handle scroll */
            /* padding-right: 10px; */ /* Space for scrollbar - Removed */
            /* padding-left: 5px; */ /* Minor padding for content - Removed */
        `;
        // Add a heading for the section (optional)
        const themeSectionHeading = document.createElement('h4');
        themeSectionHeading.textContent = '► Theme'; // Changed text and added indicator
        themeSectionHeading.style.cssText = `
            margin-top: 0;
            margin-bottom: 10px;
            border-bottom: 1px solid #555;
            padding-bottom: 5px;
            cursor: pointer;
            user-select: none;
        `;
        themeSection.appendChild(themeSectionHeading);

        // Create a container for the actual theme options, to be toggled
        const themeOptionsContainer = document.createElement('div');
        themeOptionsContainer.id = 'otk-theme-options-container';
        themeOptionsContainer.style.display = 'none'; // Hidden by default
        // Apply scrolling properties to this container instead of themeSection directly
        themeOptionsContainer.style.cssText += `
            display: none; /* Reiterate, will be toggled */
            flex-direction: column;
            /* gap: 10px; Will be handled by margins/padding of new structure or individual rows */
            max-height: 300px; /* Adjusted from themeSection's previous max-height */
            overflow-y: auto;
            padding-right: 20px; /* Further Increased right padding for scrollbar clearance (15px + 5px) */
            box-sizing: border-box; /* Ensure padding is included */
            /* padding-left: 5px; */ /* Minor padding for content - Remains Removed, covered by contentArea */
        `;
        themeSection.appendChild(themeOptionsContainer);

        sectionsContainer.appendChild(themeSection); // Add theme section to main content

        document.body.appendChild(optionsWindow);

        // Event listener for toggling theme options visibility
        themeSectionHeading.addEventListener('click', () => {
            const isHidden = themeOptionsContainer.style.display === 'none';
            if (isHidden) {
                themeOptionsContainer.style.display = 'flex'; // Use 'flex' as it's a flex container
                themeSectionHeading.textContent = '▼ Theme';
            } else {
                themeOptionsContainer.style.display = 'none';
                themeSectionHeading.textContent = '► Theme';
            }
        });

        // Helper function to create a checkbox option row
        function createCheckboxOptionRow(options) {
            // options = { labelText, storageKey, defaultValue, idSuffix, requiresRerender }
            const group = document.createElement('div');
            group.style.cssText = `
                display: flex;
                align-items: center;
                gap: 8px;
                width: 100%;
                margin-bottom: 5px;
            `;

            const label = document.createElement('label');
            label.textContent = options.labelText;
            label.htmlFor = `otk-${options.idSuffix}-checkbox`;
            label.style.cssText = `
                font-size: 12px;
                text-align: left;
                flex-basis: 230px;
                flex-shrink: 0;
            `;

            const controlsWrapperDiv = document.createElement('div');
            controlsWrapperDiv.style.cssText = `
                display: flex;
                flex-grow: 1;
                align-items: center;
                justify-content: flex-end; /* Align checkbox to the right */
                min-width: 0;
            `;

            const checkbox = document.createElement('input');
            checkbox.type = 'checkbox';
            checkbox.id = `otk-${options.idSuffix}-checkbox`;
            checkbox.style.cssText = `
                height: 16px;
                width: 16px;
                flex-shrink: 0;
            `;

            // Initialize checkbox state from theme settings
            const settings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
            const savedValue = settings[options.storageKey];
            checkbox.checked = (savedValue !== undefined) ? savedValue : options.defaultValue;

            checkbox.addEventListener('change', () => {
                saveThemeSetting(options.storageKey, checkbox.checked, options.requiresRerender);
            });

            controlsWrapperDiv.appendChild(checkbox);
            group.appendChild(label);
            group.appendChild(controlsWrapperDiv);
            return group;
        }

        // Helper function to create a theme option row
        function createThemeOptionRow(options) {
            // options = { labelText, storageKey, cssVariable, defaultValue, inputType ('color'|'number'), unit ('px'|null), min, max, idSuffix }
            const group = document.createElement('div');
            // Using Flexbox for more dynamic sizing
            group.style.cssText = `
                display: flex;
                align-items: center; /* Vertically align label and controls-wrapper */
                gap: 8px; /* Space between label and controls-wrapper */
                width: 100%;
                margin-bottom: 5px;
            `;

            const label = document.createElement('label');
            label.textContent = options.labelText;
            label.htmlFor = `otk-${options.idSuffix}`; // Points to the main input (picker or number input)
            label.style.cssText = `
                font-size: 12px;
                text-align: left;
                flex-basis: 230px; /* Accommodate longest label */
                flex-shrink: 0; /* Prevent shrinking */
            `;

            // Create a wrapper for all controls (hex, main input, button)
            const controlsWrapperDiv = document.createElement('div');
            controlsWrapperDiv.style.cssText = `
                display: flex;
                flex-grow: 1; /* Take remaining space */
                align-items: center; /* Vertically align controls */
                gap: 8px; /* Space between controls */
                min-width: 0; /* Allow shrinking if needed */
            `;

            let hexInput = null;
            if (options.inputType === 'color') {
                hexInput = document.createElement('input');
                hexInput.type = 'text';
                hexInput.id = `otk-${options.idSuffix}-hex`;
                hexInput.style.cssText = `
                    flex: 1 1 70px; /* flex-grow, flex-shrink, flex-basis */
                    min-width: 50px;
                    height: 25px;
                    box-sizing: border-box;
                    font-size: 12px;
                    text-align: right;
                `;
            }

            const mainInput = document.createElement('input');
            mainInput.type = options.inputType;
            mainInput.id = `otk-${options.idSuffix}`;
            if (options.inputType === 'color') {
                mainInput.style.cssText = `
                    flex-grow: 0;
                    flex-shrink: 0;
                    width: 30px; /* Adjusted width */
                    height: 25px;
                    padding: 1px; /* Adjusted padding */
                    box-sizing: border-box;
                `;
            } else if (options.inputType === 'number') {
                mainInput.style.cssText = `
                    flex: 1 1 60px; /* flex-grow, flex-shrink, flex-basis */
                    min-width: 40px;
                    height: 25px;
                    box-sizing: border-box;
                    font-size: 12px;
                `;
                // Add text-align: right for number inputs created by createThemeOptionRow
                if (options.inputType === 'number') {
                    mainInput.style.textAlign = 'right';
                }
                if (options.min !== undefined) mainInput.min = options.min;
                if (options.max !== undefined) mainInput.max = options.max;
            }

            const defaultBtn = document.createElement('button');
            defaultBtn.textContent = 'Default';
            defaultBtn.style.cssText = `
                flex-grow: 0;
                flex-shrink: 0;
                padding: 2px 6px; /* Adjusted padding */
                height: 25px;
                font-size: 11px;
                box-sizing: border-box;
                width: auto;
            `;

            group.appendChild(label);

            // Append controls to their wrapper
            if (hexInput) {
                controlsWrapperDiv.appendChild(hexInput);
            }
            controlsWrapperDiv.appendChild(mainInput);
            controlsWrapperDiv.appendChild(defaultBtn);

            group.appendChild(controlsWrapperDiv); // Append the wrapper to the main group

            // Determine initial value for inputs
            let initialValue = getComputedStyle(document.documentElement).getPropertyValue(options.cssVariable)?.trim() || options.defaultValue;
            if (options.unit && initialValue.endsWith(options.unit)) {
                initialValue = initialValue.replace(options.unit, '');
            }

            if (options.inputType === 'color') {
                if (hexInput) hexInput.value = initialValue;
                mainInput.value = initialValue; // Color picker also needs full hex
            } else if (options.inputType === 'number') {
                mainInput.value = initialValue;
            } else if (options.inputType === 'text') {
                mainInput.value = initialValue;
            }

            // Event handling
            const updateSetting = (value, fromColorPicker = false) => { // Added fromColorPicker flag
                let processedValue = value.trim();
                if (options.inputType === 'color') {
                    if (processedValue === '') {
                        // Allow empty string to clear the color
                    } else if (!/^#[0-9A-F]{6}$/i.test(processedValue) && !/^#[0-9A-F]{3}$/i.test(processedValue)) {
                        consoleWarn(`Invalid hex color for ${options.labelText}:`, processedValue);
                        // Restore previous valid values if possible, or default
                        let currentSaved = options.defaultValue;
                        try {
                            currentSaved = (JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {})[options.storageKey] || options.defaultValue;
                        } catch (e) {
                            consoleError("Error parsing theme settings from localStorage:", e);
                        }
                        if (hexInput) hexInput.value = currentSaved;
                        mainInput.value = currentSaved;
                        return;
                    }
                    // If the update is coming from the color picker, hexInput.value is already correct via its own listener.
                    // If the update is from hexInput, update mainInput (color picker).
                    if (!fromColorPicker && hexInput) mainInput.value = processedValue;
                    // If the update is from color picker, update hexInput.
                    if (fromColorPicker && hexInput) hexInput.value = processedValue;

                } else if (options.inputType === 'number') {
                    const numValue = parseFloat(processedValue);
                    if (isNaN(numValue) || (options.min !== undefined && numValue < options.min) || (options.max !== undefined && numValue > options.max)) {
                        consoleWarn(`Invalid number value for ${options.labelText}:`, processedValue);
                         let currentSaved = options.defaultValue;
                         try {
                            currentSaved = (JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {})[options.storageKey] || options.defaultValue;
                         } catch (e) {
                            consoleError("Error parsing theme settings from localStorage:", e);
                         }
                        mainInput.value = currentSaved.replace(options.unit || '', '');
                        return;
                    }
                    mainInput.value = numValue; // Update input with validated number
                    processedValue = numValue + (options.unit || '');
                }

                if (options.storageKey === 'viewerQuote1HeaderBorderColor' || options.storageKey === 'viewerQuote2plusHeaderBorderColor') {
                    consoleLog(`[Debug UpdateSetting] Applying to ${options.cssVariable}: ${processedValue} (StorageKey: ${options.storageKey})`);
                }

                document.documentElement.style.setProperty(options.cssVariable, processedValue || 'transparent');
                saveThemeSetting(options.storageKey, processedValue);
                // If this is the cog icon color, update it directly as it's not part of applyThemeSettings' normal flow for self-update
                if (options.storageKey === 'cogIconColor') {
                     const cogIcon = document.getElementById('otk-settings-cog');
                     if(cogIcon) cogIcon.style.color = processedValue;
                }
            };

            if (hexInput) { // For color inputs
                hexInput.addEventListener('input', (e) => { // Real-time update from hex input to color picker
                    const hexValue = e.target.value.trim();
                    // Basic validation for a complete hex code (3, 4, 6, or 8 digits after #)
                    if (/^#([0-9A-F]{3}|[0-9A-F]{4}|[0-9A-F]{6}|[0-9A-F]{8})$/i.test(hexValue)) {
                        mainInput.value = hexValue;
                    }
                    // The 'change' listener below will handle full validation and saving.
                });
                hexInput.addEventListener('change', (e) => updateSetting(e.target.value, false)); // Fire on change (blur/enter) for saving

                mainInput.addEventListener('input', (e) => { // Color picker updates continuously
                    const pickerValue = e.target.value;
                    // Update hex field immediately as picker changes, assuming pickerValue is standard hex
                    if (pickerValue.startsWith('#')) { // Basic check that it's likely a hex color string
                        hexInput.value = pickerValue;
                    } else {
                        // This case should ideally not happen with standard browser behavior.
                        // If pickerValue is not hex (e.g., 'rgb(r,g,b)'), we might need to convert it or log an error.
                        // For now, we'll only update hexInput if it looks like hex.
                        // The robust validation and saving happens on 'change'.
                        consoleWarn(`Color picker returned non-hex value during input: ${pickerValue}. Hex field not updated in real-time.`);
                    }

                    // Call updateSetting to apply the change to CSS variables etc.
                    // updateSetting itself will validate the hex code before applying it.
                    updateSetting(pickerValue, true); // Pass flag true
                });
            } else { // For number inputs
                mainInput.addEventListener('change', (e) => updateSetting(e.target.value));
            }

            defaultBtn.addEventListener('click', () => {
                document.documentElement.style.removeProperty(options.cssVariable); // Reverts to CSS default
                let cssDefaultValue = getComputedStyle(document.documentElement).getPropertyValue(options.cssVariable)?.trim() || options.defaultValue;

                if (options.unit && cssDefaultValue.endsWith(options.unit)) {
                    cssDefaultValue = cssDefaultValue.replace(options.unit, '');
                }
                if (options.inputType === 'color') {
                    if (hexInput) hexInput.value = cssDefaultValue;
                    mainInput.value = cssDefaultValue;
                } else {
                    mainInput.value = cssDefaultValue;
                }
                saveThemeSetting(options.storageKey, null, options.requiresRerender);
                // If this is the cog icon color, update it directly
                if (options.storageKey === 'cogIconColor') {
                     const cogIcon = document.getElementById('otk-settings-cog');
                     if(cogIcon) cogIcon.style.color = ''; // Clear inline style to use CSS var
                }
            });
            // Initial application from saved settings (if any) is handled by applyThemeSettings call later.
            // This function just sets up the row and its default state based on current CSS or fallback.
            return group;
        }

        function createDivider() {
            const hr = document.createElement('hr');
            hr.style.cssText = "width: 100%; border: none; border-top: 1px solid #555; margin: 12px 0 8px 0;";
            return hr;
        }

        function createSectionHeading(text) {
            const h = document.createElement('h5');
            h.textContent = text;
            // Adjusted margins for more space, removed border-bottom
            h.style.cssText = "margin-top: 10px; margin-bottom: 6px; color: #cccccc; font-size: 13px; padding-bottom: 4px; font-weight: bold; text-align: left;";
            return h;
        }

        // Clear existing content from themeOptionsContainer before repopulating
        themeOptionsContainer.innerHTML = '';

        // --- GUI Section ---
        const guiSectionHeading = createSectionHeading('GUI');
        guiSectionHeading.style.marginTop = "0px"; // First heading doesn't need extra top margin
        guiSectionHeading.style.marginBottom = "18px"; // Increased bottom margin for specific space after GUI heading
        themeOptionsContainer.appendChild(guiSectionHeading);
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Background:", storageKey: 'guiBgColor', cssVariable: '--otk-gui-bg-color', defaultValue: '#181818', inputType: 'color', idSuffix: 'gui-bg' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Title Text:", storageKey: 'titleTextColor', cssVariable: '--otk-title-text-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'title-text' }));

        const threadListDisplaySubHeading = createSectionHeading('Thread List Display');
        themeOptionsContainer.appendChild(threadListDisplaySubHeading);

        themeOptionsContainer.appendChild(createColorOrNoneOptionRow({ labelText: "Thread Box Outline:", storageKey: 'guiThreadBoxOutlineColor', defaultValue: 'none', idSuffix: 'gui-thread-box-outline' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Thread Titles Text:", storageKey: 'guiThreadListTitleColor', cssVariable: '--otk-gui-threadlist-title-color', defaultValue: '#e0e0e0', inputType: 'color', idSuffix: 'threadlist-title' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Thread Times Text:", storageKey: 'guiThreadListTimeColor', cssVariable: '--otk-gui-threadlist-time-color', defaultValue: '#aaa', inputType: 'color', idSuffix: 'threadlist-time' }));

        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Time Position:',
            storageKey: 'otkThreadTimePosition',
            options: ['After Title', 'Before Title'],
            defaultValue: 'Before Title',
            requiresRerender: false
        }));

        const dividerCheckboxRow = createCheckboxOptionRow({
            labelText: "Enable Divider:",
            storageKey: 'otkThreadTimeDividerEnabled',
            defaultValue: true,
            idSuffix: 'thread-time-divider-enable'
        });
        themeOptionsContainer.appendChild(dividerCheckboxRow);

        const dividerSymbolRow = createThemeOptionRow({
            labelText: "Divider Symbol:",
            storageKey: 'otkThreadTimeDividerSymbol',
            cssVariable: '--otk-thread-time-divider-symbol',
            defaultValue: '|',
            inputType: 'text',
            idSuffix: 'thread-time-divider-symbol'
        });
        themeOptionsContainer.appendChild(dividerSymbolRow);

        const dividerColorRow = createThemeOptionRow({
            labelText: "Divider Color:",
            storageKey: 'otkThreadTimeDividerColor',
            cssVariable: '--otk-thread-time-divider-color',
            defaultValue: '#ff8040',
            inputType: 'color',
            idSuffix: 'thread-time-divider-color'
        });
        themeOptionsContainer.appendChild(dividerColorRow);

        const dividerCheckbox = dividerCheckboxRow.querySelector('input[type="checkbox"]');
        const updateDividerOptionsVisibility = () => {
            const isEnabled = dividerCheckbox.checked;
            dividerSymbolRow.style.display = isEnabled ? 'flex' : 'none';
            dividerColorRow.style.display = isEnabled ? 'flex' : 'none';
        };

        dividerCheckbox.addEventListener('change', updateDividerOptionsVisibility);

        // Initial call to set visibility based on saved state
        setTimeout(updateDividerOptionsVisibility, 0);

        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Bracket Style:',
            storageKey: 'otkThreadTimeBracketStyle',
            options: ['[]', '()', 'none'],
            defaultValue: '[]',
            requiresRerender: false
        }));

        themeOptionsContainer.appendChild(createThemeOptionRow({
            labelText: "Bracket Color:",
            storageKey: 'otkThreadTimeBracketColor',
            cssVariable: '--otk-thread-time-bracket-color',
            defaultValue: '#aaa',
            inputType: 'color',
            idSuffix: 'thread-time-bracket-color'
        }));

        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Stats Text:", storageKey: 'actualStatsTextColor', cssVariable: '--otk-stats-text-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'actual-stats-text' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Stats Dash:", storageKey: 'statsDashColor', cssVariable: '--otk-stats-dash-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'stats-dash' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Background Updates Stats Text:", storageKey: 'backgroundUpdatesStatsTextColor', cssVariable: '--otk-background-updates-stats-text-color', defaultValue: '#FFD700', inputType: 'color', idSuffix: 'background-updates-stats-text' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Cog Icon:", storageKey: 'cogIconColor', cssVariable: '--otk-cog-icon-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'cog-icon' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Countdown Background:", storageKey: 'countdownBgColor', cssVariable: '--otk-countdown-bg-color', defaultValue: '#181818', inputType: 'color', idSuffix: 'countdown-bg' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Countdown Label Text:", storageKey: 'countdownLabelTextColor', cssVariable: '--otk-countdown-label-text-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'countdown-label-text' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Countdown Timer Text:", storageKey: 'countdownTimerTextColor', cssVariable: '--otk-countdown-timer-text-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'countdown-timer-text' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Separator:", storageKey: 'separatorColor', cssVariable: '--otk-separator-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'separator' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Clock Background:", storageKey: 'clockBgColor', cssVariable: '--otk-clock-bg-color', defaultValue: '', inputType: 'color', idSuffix: 'clock-bg' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Clock Text:", storageKey: 'clockTextColor', cssVariable: '--otk-clock-text-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'clock-text' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Clock Border:", storageKey: 'clockBorderColor', cssVariable: '--otk-clock-border-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'clock-border' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Clock Divider:", storageKey: 'clockDividerColor', cssVariable: '--otk-clock-divider-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'clock-divider' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Clock Cog Icon:", storageKey: 'clockCogColor', cssVariable: '--otk-clock-cog-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'clock-cog' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Clock Search Background:", storageKey: 'clockSearchBgColor', cssVariable: '--otk-clock-search-bg-color', defaultValue: '#333', inputType: 'color', idSuffix: 'clock-search-bg' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Clock Search Text:", storageKey: 'clockSearchTextColor', cssVariable: '--otk-clock-search-text-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'clock-search-text' }));

        // Sub-section for GUI Buttons
        const guiButtonsSubHeading = document.createElement('h6');
        guiButtonsSubHeading.textContent = "GUI Buttons";
        guiButtonsSubHeading.style.cssText = "margin-top: 20px; margin-bottom: 15px; color: #cccccc; font-size: 12px; font-weight: bold; text-align: left;"; // Increased margin-top and margin-bottom
        themeOptionsContainer.appendChild(guiButtonsSubHeading);
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Background:", storageKey: 'guiButtonBgColor', cssVariable: '--otk-button-bg-color', defaultValue: '#555555', inputType: 'color', idSuffix: 'gui-button-bg' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Text:", storageKey: 'guiButtonTextColor', cssVariable: '--otk-button-text-color', defaultValue: '#ffffff', inputType: 'color', idSuffix: 'gui-button-text' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Border:", storageKey: 'guiButtonBorderColor', cssVariable: '--otk-button-border-color', defaultValue: '#777777', inputType: 'color', idSuffix: 'gui-button-border' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Hover Background:", storageKey: 'guiButtonHoverBgColor', cssVariable: '--otk-button-hover-bg-color', defaultValue: '#666666', inputType: 'color', idSuffix: 'gui-button-hover-bg' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Active Background:", storageKey: 'guiButtonActiveBgColor', cssVariable: '--otk-button-active-bg-color', defaultValue: '#444444', inputType: 'color', idSuffix: 'gui-button-active-bg' }));

        // themeOptionsContainer.appendChild(createDivider()); // Removed divider

        // --- GUI Background Section ---
        const guiBackgroundSubHeading = document.createElement('h6');
        guiBackgroundSubHeading.textContent = "GUI Background";
        guiBackgroundSubHeading.style.cssText = "margin-top: 20px; margin-bottom: 15px; color: #cccccc; font-size: 12px; font-weight: bold; text-align: left;";
        themeOptionsContainer.appendChild(guiBackgroundSubHeading);

        const bgImageUrlRow = document.createElement('div');
        bgImageUrlRow.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const bgImageUrlLabel = document.createElement('label');
        bgImageUrlLabel.textContent = 'Background Image URL:';
        bgImageUrlLabel.htmlFor = 'otk-gui-bg-image-url-input';
        bgImageUrlLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const bgImageUrlControlsWrapper = document.createElement('div');
        bgImageUrlControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0;";

        const bgImageUrlInput = document.createElement('input');
        bgImageUrlInput.type = 'text';
        bgImageUrlInput.id = 'otk-gui-bg-image-url-input';
        bgImageUrlInput.placeholder = 'Enter image URL or browse';
        bgImageUrlInput.style.cssText = "flex-grow: 1; height: 25px; box-sizing: border-box; font-size: 12px; text-align: left;";

        const initialBgUrl = (JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {}).guiBackgroundImageUrl || '';
        if (initialBgUrl.startsWith('data:image')) {
            bgImageUrlInput.value = '(Local file is selected)';
            bgImageUrlInput.dataset.fullUrl = initialBgUrl;
        } else {
            bgImageUrlInput.value = initialBgUrl;
        }

        bgImageUrlInput.addEventListener('input', () => {
            bgImageUrlInput.dataset.fullUrl = '';
        });

        bgImageUrlInput.addEventListener('change', () => {
            const valueToSave = bgImageUrlInput.dataset.fullUrl || bgImageUrlInput.value;
            saveThemeSetting('guiBackgroundImageUrl', valueToSave, false);
            applyThemeSettings({ forceRerender: false });
        });

        const browseButton = document.createElement('button');
        browseButton.textContent = "Browse...";
        browseButton.style.cssText = "height: 25px; flex-shrink: 0; padding: 2px 6px; font-size: 11px;";

        const fileInput = document.createElement('input');
        fileInput.type = 'file';
        fileInput.accept = 'image/*';
        fileInput.style.display = 'none';

        browseButton.addEventListener('click', (e) => {
            e.preventDefault();
            fileInput.click();
        });

        fileInput.addEventListener('change', (event) => {
            const file = event.target.files[0];
            if (file) {
                const reader = new FileReader();
                reader.onload = (e) => {
                    const dataUrl = e.target.result;
                    bgImageUrlInput.value = `(Local file: ${file.name})`;
                    bgImageUrlInput.dataset.fullUrl = dataUrl;
                    bgImageUrlInput.dispatchEvent(new Event('change'));
                };
                reader.readAsDataURL(file);
            }
        });

        bgImageUrlControlsWrapper.appendChild(bgImageUrlInput);
        bgImageUrlControlsWrapper.appendChild(browseButton);
        bgImageUrlControlsWrapper.appendChild(fileInput);

        bgImageUrlRow.appendChild(bgImageUrlLabel);
        bgImageUrlRow.appendChild(bgImageUrlControlsWrapper);

        themeOptionsContainer.appendChild(bgImageUrlRow);

        function createDropdownRow(options) {
            const group = document.createElement('div');
            group.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";
            const label = document.createElement('label');
            label.textContent = options.labelText;
            label.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";
            const controlsWrapperDiv = document.createElement('div');
            controlsWrapperDiv.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0;";
            const select = document.createElement('select');
            select.style.cssText = "width: 100%; height: 25px; box-sizing: border-box; font-size: 12px;";
            options.options.forEach(opt => {
                const optionElement = document.createElement('option');
                optionElement.value = opt;
                optionElement.textContent = opt;
                select.appendChild(optionElement);
            });
            select.value = (JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {})[options.storageKey] || options.defaultValue;
            select.addEventListener('change', () => {
                saveThemeSetting(options.storageKey, select.value, options.requiresRerender || false);
                 if (!options.requiresRerender) {
                    applyThemeSettings({ forceRerender: false });
                }
            });
            controlsWrapperDiv.appendChild(select);
            group.appendChild(label);
            group.appendChild(controlsWrapperDiv);
            return group;
        }

        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Background Size:',
            storageKey: 'guiBgSize',
            options: ['auto', 'cover', 'contain'],
            defaultValue: 'cover',
            requiresRerender: false
        }));
        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Background Repeat:',
            storageKey: 'guiBgRepeat',
            options: ['no-repeat', 'repeat', 'repeat-x', 'repeat-y'],
            defaultValue: 'no-repeat',
            requiresRerender: false
        }));
        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Background Position:',
            storageKey: 'guiBgPosition',
            options: ['center', 'top', 'bottom', 'left', 'right'],
            defaultValue: 'center',
            requiresRerender: false
        }));

        // --- Viewer Background Section ---
        const viewerBackgroundSubHeading = document.createElement('h6');
        viewerBackgroundSubHeading.textContent = "Viewer Background";
        viewerBackgroundSubHeading.style.cssText = "margin-top: 20px; margin-bottom: 15px; color: #cccccc; font-size: 12px; font-weight: bold; text-align: left;";
        themeOptionsContainer.appendChild(viewerBackgroundSubHeading);

        const viewerBgImageUrlRow = document.createElement('div');
        viewerBgImageUrlRow.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const viewerBgImageUrlLabel = document.createElement('label');
        viewerBgImageUrlLabel.textContent = 'Background Image URL:';
        viewerBgImageUrlLabel.htmlFor = 'otk-viewer-bg-image-url-input';
        viewerBgImageUrlLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const viewerBgImageUrlControlsWrapper = document.createElement('div');
        viewerBgImageUrlControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0;";

        const viewerBgImageUrlInput = document.createElement('input');
        viewerBgImageUrlInput.type = 'text';
        viewerBgImageUrlInput.id = 'otk-viewer-bg-image-url-input';
        viewerBgImageUrlInput.placeholder = 'Enter image URL or browse';
        viewerBgImageUrlInput.style.cssText = "flex-grow: 1; height: 25px; box-sizing: border-box; font-size: 12px; text-align: left;";

        const initialViewerBgUrl = (JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {}).viewerBackgroundImageUrl || '';
        if (initialViewerBgUrl.startsWith('data:image')) {
            viewerBgImageUrlInput.value = '(Local file is selected)';
            viewerBgImageUrlInput.dataset.fullUrl = initialViewerBgUrl;
        } else {
            viewerBgImageUrlInput.value = initialViewerBgUrl;
        }

        viewerBgImageUrlInput.addEventListener('input', () => {
            viewerBgImageUrlInput.dataset.fullUrl = '';
        });

        viewerBgImageUrlInput.addEventListener('change', () => {
            const valueToSave = viewerBgImageUrlInput.dataset.fullUrl || viewerBgImageUrlInput.value;
            saveThemeSetting('viewerBackgroundImageUrl', valueToSave, false);
            applyThemeSettings({ forceRerender: false });
        });

        const viewerBrowseButton = document.createElement('button');
        viewerBrowseButton.textContent = "Browse...";
        viewerBrowseButton.style.cssText = "height: 25px; flex-shrink: 0; padding: 2px 6px; font-size: 11px;";

        const viewerFileInput = document.createElement('input');
        viewerFileInput.type = 'file';
        viewerFileInput.accept = 'image/*';
        viewerFileInput.style.display = 'none';

        viewerBrowseButton.addEventListener('click', (e) => {
            e.preventDefault();
            viewerFileInput.click();
        });

        viewerFileInput.addEventListener('change', (event) => {
            const file = event.target.files[0];
            if (file) {
                const reader = new FileReader();
                reader.onload = (e) => {
                    const dataUrl = e.target.result;
                    viewerBgImageUrlInput.value = `(Local file: ${file.name})`;
                    viewerBgImageUrlInput.dataset.fullUrl = dataUrl;
                    viewerBgImageUrlInput.dispatchEvent(new Event('change'));
                };
                reader.readAsDataURL(file);
            }
        });

        viewerBgImageUrlControlsWrapper.appendChild(viewerBgImageUrlInput);
        viewerBgImageUrlControlsWrapper.appendChild(viewerBrowseButton);
        viewerBgImageUrlControlsWrapper.appendChild(viewerFileInput);

        viewerBgImageUrlRow.appendChild(viewerBgImageUrlLabel);
        viewerBgImageUrlRow.appendChild(viewerBgImageUrlControlsWrapper);

        themeOptionsContainer.appendChild(viewerBgImageUrlRow);

        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Background Size:',
            storageKey: 'viewerBgSize',
            options: ['auto', 'cover', 'contain'],
            defaultValue: 'cover',
            requiresRerender: false
        }));
        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Background Repeat:',
            storageKey: 'viewerBgRepeat',
            options: ['no-repeat', 'repeat', 'repeat-x', 'repeat-y'],
            defaultValue: 'no-repeat',
            requiresRerender: false
        }));
        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Background Position:',
            storageKey: 'viewerBgPosition',
            options: ['center', 'top', 'bottom', 'left', 'right'],
            defaultValue: 'center',
            requiresRerender: false
        }));

        // --- PiP Background Section ---
        const pipBackgroundSubHeading = document.createElement('h6');
        pipBackgroundSubHeading.textContent = "PiP Background";
        pipBackgroundSubHeading.style.cssText = "margin-top: 20px; margin-bottom: 15px; color: #cccccc; font-size: 12px; font-weight: bold; text-align: left;";
        themeOptionsContainer.appendChild(pipBackgroundSubHeading);

        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Background:", storageKey: 'pipBackgroundColor', cssVariable: '--otk-pip-bg-color', defaultValue: '#1a1a1a', inputType: 'color', idSuffix: 'pip-bg' }));

        const pipBgImageUrlRow = document.createElement('div');
        pipBgImageUrlRow.style.cssText = "display: flex; align-items: center; gap: 8px; width: 100%; margin-bottom: 5px;";

        const pipBgImageUrlLabel = document.createElement('label');
        pipBgImageUrlLabel.textContent = 'Background Image URL:';
        pipBgImageUrlLabel.htmlFor = 'otk-pip-bg-image-url-input';
        pipBgImageUrlLabel.style.cssText = "font-size: 12px; text-align: left; flex-basis: 230px; flex-shrink: 0;";

        const pipBgImageUrlControlsWrapper = document.createElement('div');
        pipBgImageUrlControlsWrapper.style.cssText = "display: flex; flex-grow: 1; align-items: center; gap: 8px; min-width: 0;";

        const pipBgImageUrlInput = document.createElement('input');
        pipBgImageUrlInput.type = 'text';
        pipBgImageUrlInput.id = 'otk-pip-bg-image-url-input';
        pipBgImageUrlInput.placeholder = 'Enter image URL or browse';
        pipBgImageUrlInput.style.cssText = "flex-grow: 1; height: 25px; box-sizing: border-box; font-size: 12px; text-align: left;";

        const initialPipBgUrl = (JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {}).pipBackgroundImageUrl || '';
        if (initialPipBgUrl.startsWith('data:image')) {
            pipBgImageUrlInput.value = '(Local file is selected)';
            pipBgImageUrlInput.dataset.fullUrl = initialPipBgUrl;
        } else {
            pipBgImageUrlInput.value = initialPipBgUrl;
        }

        pipBgImageUrlInput.addEventListener('input', () => {
            pipBgImageUrlInput.dataset.fullUrl = '';
        });

        pipBgImageUrlInput.addEventListener('change', () => {
            const valueToSave = pipBgImageUrlInput.dataset.fullUrl || pipBgImageUrlInput.value;
            saveThemeSetting('pipBackgroundImageUrl', valueToSave, false);
            applyThemeSettings({ forceRerender: false });
        });

        const pipBrowseButton = document.createElement('button');
        pipBrowseButton.textContent = "Browse...";
        pipBrowseButton.style.cssText = "height: 25px; flex-shrink: 0; padding: 2px 6px; font-size: 11px;";

        const pipFileInput = document.createElement('input');
        pipFileInput.type = 'file';
        pipFileInput.accept = 'image/*';
        pipFileInput.style.display = 'none';

        pipBrowseButton.addEventListener('click', (e) => {
            e.preventDefault();
            pipFileInput.click();
        });

        pipFileInput.addEventListener('change', (event) => {
            const file = event.target.files[0];
            if (file) {
                const reader = new FileReader();
                reader.onload = (e) => {
                    const dataUrl = e.target.result;
                    pipBgImageUrlInput.value = `(Local file: ${file.name})`;
                    pipBgImageUrlInput.dataset.fullUrl = dataUrl;
                    pipBgImageUrlInput.dispatchEvent(new Event('change'));
                };
                reader.readAsDataURL(file);
            }
        });

        pipBgImageUrlControlsWrapper.appendChild(pipBgImageUrlInput);
        pipBgImageUrlControlsWrapper.appendChild(pipBrowseButton);
        pipBgImageUrlControlsWrapper.appendChild(pipFileInput);

        pipBgImageUrlRow.appendChild(pipBgImageUrlLabel);
        pipBgImageUrlRow.appendChild(pipBgImageUrlControlsWrapper);

        themeOptionsContainer.appendChild(pipBgImageUrlRow);

        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Background Size:',
            storageKey: 'pipBgSize',
            options: ['auto', 'cover', 'contain'],
            defaultValue: 'cover',
            requiresRerender: false
        }));
        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Background Repeat:',
            storageKey: 'pipBgRepeat',
            options: ['no-repeat', 'repeat', 'repeat-x', 'repeat-y'],
            defaultValue: 'no-repeat',
            requiresRerender: false
        }));
        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'Background Position:',
            storageKey: 'pipBgPosition',
            options: ['center', 'top', 'bottom', 'left', 'right'],
            defaultValue: 'center',
            requiresRerender: false
        }));


        // --- Viewer Section ---
        const viewerSectionHeading = createSectionHeading('Viewer');
        viewerSectionHeading.style.marginTop = "22px"; // Increased top margin for space before Viewer heading
        viewerSectionHeading.style.marginBottom = "18px"; // Increased bottom margin for space after Viewer heading
        themeOptionsContainer.appendChild(viewerSectionHeading);

        // Add Message Layout Dropdown to Viewer section (moved to top)

        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Background:", storageKey: 'viewerBgColor', cssVariable: '--otk-viewer-bg-color', defaultValue: '#181818', inputType: 'color', idSuffix: 'viewer-bg' }));
        themeOptionsContainer.appendChild(createColorOrNoneOptionRow({ labelText: "Viewer Thread Box Outline:", storageKey: 'viewerThreadBoxOutlineColor', defaultValue: 'none', idSuffix: 'viewer-thread-box-outline' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "GUI Bottom Border:", storageKey: 'guiBottomBorderColor', cssVariable: '--otk-gui-bottom-border-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'gui-bottom-border' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "New Messages Divider:", storageKey: 'newMessagesDividerColor', cssVariable: '--otk-new-messages-divider-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'new-msg-divider' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "New Messages Text:", storageKey: 'newMessagesFontColor', cssVariable: '--otk-new-messages-font-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'new-msg-font' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "'Blocked Content' Font:", storageKey: 'blockedContentFontColor', cssVariable: '--otk-blocked-content-font-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'blocked-content-font' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "New Messages Font Size (px):", storageKey: 'newMessagesFontSize', cssVariable: '--otk-new-messages-font-size', defaultValue: '16px', inputType: 'number', unit: 'px', min: 8, max: 24, idSuffix: 'new-msg-font-size', requiresRerender: false }));
        themeOptionsContainer.appendChild(createDropdownRow({
            labelText: 'New Msgs Separator Align:',
            storageKey: 'otkNewMessagesSeparatorAlignment',
            options: ['Left', 'Center', 'Right'],
            defaultValue: 'Left',
            requiresRerender: false
        }));

        // Anchor Highlight Colors
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Anchor Highlight Background:", storageKey: 'anchorHighlightBgColor', cssVariable: '--otk-anchor-highlight-bg-color', defaultValue: '#4a4a3a', inputType: 'color', idSuffix: 'anchor-bg', requiresRerender: true }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Anchor Highlight Border:", storageKey: 'anchorHighlightBorderColor', cssVariable: '--otk-anchor-highlight-border-color', defaultValue: '#FFD700', inputType: 'color', idSuffix: 'anchor-border', requiresRerender: true }));

        // '+' Icon Background
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "'+' Icon Background:", storageKey: 'plusIconBgColor', cssVariable: '--otk-plus-icon-bg-color', defaultValue: '#d9d9d9', inputType: 'color', idSuffix: 'plus-icon-bg-color', requiresRerender: false }));

        // Icon Colors
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Blur Icon Color:", storageKey: 'blurIconColor', cssVariable: '--otk-blur-icon-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'blur-icon' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Blur Icon Background:", storageKey: 'blurIconBgColor', cssVariable: '--otk-blur-icon-bg-color', defaultValue: '#d9d9d9', inputType: 'color', idSuffix: 'blur-icon-bg' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Resize Icon Color:", storageKey: 'resizeIconColor', cssVariable: '--otk-resize-icon-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'resize-icon' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Resize Icon Background:", storageKey: 'resizeIconBgColor', cssVariable: '--otk-resize-icon-bg-color', defaultValue: '#d9d9d9', inputType: 'color', idSuffix: 'resize-icon-bg' }));

        const imageBlurSectionHeading = createSectionHeading('Image Blurring');
        imageBlurSectionHeading.style.marginTop = "22px";
        imageBlurSectionHeading.style.marginBottom = "18px";
        themeOptionsContainer.appendChild(imageBlurSectionHeading);

        const blurGroup = document.createElement('div');
        blurGroup.style.cssText = `
            display: flex;
            align-items: center;
            gap: 8px;
            width: 100%;
            margin-bottom: 5px;
        `;

        const blurLabel = document.createElement('label');
        blurLabel.textContent = "Blur Amount (%):";
        blurLabel.htmlFor = `otk-image-blur-amount`;
        blurLabel.style.cssText = `
            font-size: 12px;
            text-align: left;
            flex-basis: 230px;
            flex-shrink: 0;
        `;

        const blurControlsWrapper = document.createElement('div');
        blurControlsWrapper.style.cssText = `
            display: flex;
            flex-grow: 1;
            align-items: center;
            gap: 8px;
            min-width: 0;
        `;

        const blurInput = document.createElement('input');
        blurInput.type = 'number';
        blurInput.id = 'otk-image-blur-amount';
        blurInput.min = 0;
        blurInput.max = 100;
        blurInput.style.cssText = `
            flex: 1 1 60px;
            min-width: 40px;
            height: 25px;
            box-sizing: border-box;
            font-size: 12px;
            text-align: right;
        `;
        blurInput.value = localStorage.getItem(IMAGE_BLUR_AMOUNT_KEY) || '60';

        blurInput.addEventListener('change', (e) => {
            let value = parseInt(e.target.value, 10);
            if (isNaN(value) || value < 0 || value > 100) {
                value = 60; // reset to default if invalid
            }
            e.target.value = value;
            localStorage.setItem(IMAGE_BLUR_AMOUNT_KEY, value);
            consoleLog(`Image blur amount saved: ${value}%`);
        });

        const blurDefaultBtn = document.createElement('button');
        blurDefaultBtn.textContent = 'Default';
        blurDefaultBtn.style.cssText = `
            flex-grow: 0;
            flex-shrink: 0;
            padding: 2px 6px;
            height: 25px;
            font-size: 11px;
            box-sizing: border-box;
            width: auto;
        `;

        blurDefaultBtn.addEventListener('click', () => {
            blurInput.value = '60';
            localStorage.setItem(IMAGE_BLUR_AMOUNT_KEY, '60');
            consoleLog(`Image blur amount reset to default: 60%`);
        });

        blurControlsWrapper.appendChild(blurInput);
        blurControlsWrapper.appendChild(blurDefaultBtn);

        const clearBlurredBtn = document.createElement('button');
        clearBlurredBtn.textContent = 'Clear All';
        clearBlurredBtn.style.cssText = `
            flex-grow: 0;
            flex-shrink: 0;
            padding: 2px 6px;
            height: 25px;
            font-size: 11px;
            box-sizing: border-box;
            width: auto;
            background-color: #803333;
            color: white;
        `;
        clearBlurredBtn.onmouseover = () => clearBlurredBtn.style.backgroundColor = '#a04444';
        clearBlurredBtn.onmouseout = () => clearBlurredBtn.style.backgroundColor = '#803333';

        clearBlurredBtn.addEventListener('click', () => {
            if (confirm("Are you sure you want to clear all blurred images? This cannot be undone.")) {
                blurredImages.clear();
                localStorage.removeItem(BLURRED_IMAGES_KEY);

                // Remove blur from all currently blurred images on the page
                const allImagesOnPage = document.querySelectorAll('img[data-filehash]');
                allImagesOnPage.forEach(img => {
                    img.style.filter = '';
                });

                consoleLog("Cleared all blurred images.");
                alert("All blurred images have been cleared.");
            }
        });
        blurControlsWrapper.appendChild(clearBlurredBtn);

        blurGroup.appendChild(blurLabel);
        blurGroup.appendChild(blurControlsWrapper);
        themeOptionsContainer.appendChild(blurGroup);

        const tweetEmbedModeGroup = document.createElement('div');
        tweetEmbedModeGroup.style.cssText = `
            display: flex;
            align-items: center;
            gap: 8px;
            width: 100%;
            margin-bottom: 5px;
        `;
        const tweetEmbedModeLabel = document.createElement('label');
        tweetEmbedModeLabel.textContent = "Tweet Embeds:";
        tweetEmbedModeLabel.htmlFor = 'otk-tweet-embed-mode-dropdown';
        tweetEmbedModeLabel.style.cssText = `
            font-size: 12px;
            text-align: left;
            flex-basis: 230px;
            flex-shrink: 0;
        `;
        const tweetEmbedModeControlsWrapper = document.createElement('div');
        tweetEmbedModeControlsWrapper.style.cssText = `
            display: flex;
            flex-grow: 1;
            align-items: center;
        `;
        const tweetEmbedModeDropdown = document.createElement('select');
        tweetEmbedModeDropdown.id = 'otk-tweet-embed-mode-dropdown';
        tweetEmbedModeDropdown.style.cssText = `
            flex-grow: 1;
            height: 25px;
            box-sizing: border-box;
            font-size: 12px;
            text-align: center;
            text-align-last: center;
        `;
        const tweetEmbedOptions = [
            { label: 'Disabled', value: 'disabled' },
            { label: 'Default', value: 'default' },
            { label: 'Dark Mode', value: 'dark' }
        ];
        tweetEmbedOptions.forEach(opt => {
            const optionElement = document.createElement('option');
            optionElement.value = opt.value;
            optionElement.textContent = opt.label;
            tweetEmbedModeDropdown.appendChild(optionElement);
        });
        tweetEmbedModeDropdown.value = localStorage.getItem(TWEET_EMBED_MODE_KEY) || 'default';
        tweetEmbedModeDropdown.addEventListener('change', () => {
            saveThemeSetting(TWEET_EMBED_MODE_KEY, tweetEmbedModeDropdown.value, true);
        });
        tweetEmbedModeGroup.appendChild(tweetEmbedModeLabel);
        tweetEmbedModeControlsWrapper.appendChild(tweetEmbedModeDropdown);
        tweetEmbedModeGroup.appendChild(tweetEmbedModeControlsWrapper);
        themeOptionsContainer.appendChild(tweetEmbedModeGroup);

        // themeOptionsContainer.appendChild(createDivider()); // Removed divider

        // --- Messages Section Restructuring ---
        // --- Messages (Odds) Section ---
        const oddMessagesHeading = createSectionHeading('Messages (Odds)');
        oddMessagesHeading.style.marginTop = "22px";
        oddMessagesHeading.style.marginBottom = "18px";
        themeOptionsContainer.appendChild(oddMessagesHeading);
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Font Size (px):", storageKey: 'msgDepthOddContentFontSize', cssVariable: '--otk-msg-depth-odd-content-font-size', defaultValue: '16px', inputType: 'number', unit: 'px', min: 8, max: 24, idSuffix: 'msg-depth-odd-content-fontsize', requiresRerender: true }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Background:", storageKey: 'msgDepthOddBgColor', cssVariable: '--otk-msg-depth-odd-bg-color', defaultValue: '#ffffff', inputType: 'color', idSuffix: 'msg-depth-odd-bg', requiresRerender: true }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Content Font:", storageKey: 'msgDepthOddTextColor', cssVariable: '--otk-msg-depth-odd-text-color', defaultValue: '#333333', inputType: 'color', idSuffix: 'msg-depth-odd-text', requiresRerender: true }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Header Font:", storageKey: 'msgDepthOddHeaderTextColor', cssVariable: '--otk-msg-depth-odd-header-text-color', defaultValue: '#555555', inputType: 'color', idSuffix: 'msg-depth-odd-header-text', requiresRerender: true }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Header Underline:", storageKey: 'viewerHeaderBorderColorOdd', cssVariable: '--otk-viewer-header-border-color-odd', defaultValue: '#000000', inputType: 'color', idSuffix: 'viewer-header-border-odd', requiresRerender: true }));
        themeOptionsContainer.appendChild(createCheckboxOptionRow({ labelText: "Show Media Filename:", storageKey: 'showOddMessageFilename', defaultValue: false, idSuffix: 'show-odd-filename', requiresRerender: true }));

        // --- Messages (Evens) Section ---
        const evenMessagesHeading = createSectionHeading('Messages (Evens)');
        evenMessagesHeading.style.marginTop = "22px";
        evenMessagesHeading.style.marginBottom = "18px";
        themeOptionsContainer.appendChild(evenMessagesHeading);
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Font Size (px):", storageKey: 'msgDepthEvenContentFontSize', cssVariable: '--otk-msg-depth-even-content-font-size', defaultValue: '16px', inputType: 'number', unit: 'px', min: 8, max: 24, idSuffix: 'msg-depth-even-content-fontsize', requiresRerender: true }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Background:", storageKey: 'msgDepthEvenBgColor', cssVariable: '--otk-msg-depth-even-bg-color', defaultValue: '#d9d9d9', inputType: 'color', idSuffix: 'msg-depth-even-bg', requiresRerender: true }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Content Font:", storageKey: 'msgDepthEvenTextColor', cssVariable: '--otk-msg-depth-even-text-color', defaultValue: '#333333', inputType: 'color', idSuffix: 'msg-depth-even-text', requiresRerender: true }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Header Font:", storageKey: 'msgDepthEvenHeaderTextColor', cssVariable: '--otk-msg-depth-even-header-text-color', defaultValue: '#555555', inputType: 'color', idSuffix: 'msg-depth-even-header-text', requiresRerender: true }));
        themeOptionsContainer.appendChild(createCheckboxOptionRow({ labelText: "Show Media Filename:", storageKey: 'showEvenMessageFilename', defaultValue: false, idSuffix: 'show-even-filename', requiresRerender: true }));

        // --- Options Panel Section ---
        const optionsPanelSectionHeading = createSectionHeading('Options Panel');
        optionsPanelSectionHeading.style.marginTop = "22px"; // Increased top margin
        optionsPanelSectionHeading.style.marginBottom = "18px"; // Increased bottom margin
        themeOptionsContainer.appendChild(optionsPanelSectionHeading);
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Panel Text:", storageKey: 'optionsTextColor', cssVariable: '--otk-options-text-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'options-text' }));

        // --- Loading Screen Sub-Section (within Theme) ---
        const loadingScreenSubHeading = document.createElement('h6');
        loadingScreenSubHeading.textContent = "Loading Screen";
        loadingScreenSubHeading.style.cssText = "margin-top: 20px; margin-bottom: 15px; color: #cccccc; font-size: 12px; font-weight: bold; text-align: left;"; // Increased margin-top and margin-bottom
        themeOptionsContainer.appendChild(loadingScreenSubHeading);

        // Add Overlay Opacity first
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Overlay Opacity:", storageKey: 'loadingOverlayOpacity', cssVariable: '--otk-loading-overlay-opacity', defaultValue: '0.8', inputType: 'number', min:0.0, max:1.0, step:0.05, idSuffix: 'loading-overlay-opacity' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Overlay Base:", storageKey: 'loadingOverlayBaseHexColor', cssVariable: '--otk-loading-overlay-base-hex-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'loading-overlay-base-hex' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Text:", storageKey: 'loadingTextColor', cssVariable: '--otk-loading-text-color', defaultValue: '#ffffff', inputType: 'color', idSuffix: 'loading-text' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Progress Bar Background:", storageKey: 'loadingProgressBarBgColor', cssVariable: '--otk-loading-progress-bar-bg-color', defaultValue: '#333333', inputType: 'color', idSuffix: 'loading-progress-bg' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Progress Bar Fill:", storageKey: 'loadingProgressBarFillColor', cssVariable: '--otk-loading-progress-bar-fill-color', defaultValue: '#4CAF50', inputType: 'color', idSuffix: 'loading-progress-fill' }));
        themeOptionsContainer.appendChild(createThemeOptionRow({ labelText: "Progress Bar Text:", storageKey: 'loadingProgressBarTextColor', cssVariable: '--otk-loading-progress-bar-text-color', defaultValue: '#ffffff', inputType: 'color', idSuffix: 'loading-progress-text' }));

        // --- Custom Themes Section ---
        // themeOptionsContainer.appendChild(createDivider()); // Removed divider
        const customThemesSectionHeading = createSectionHeading('Custom Themes');
        customThemesSectionHeading.style.marginTop = "22px"; // Increased top margin
        customThemesSectionHeading.style.marginBottom = "18px"; // Increased bottom margin
        themeOptionsContainer.appendChild(customThemesSectionHeading);

        const customThemeActionsWrapper = document.createElement('div');
        customThemeActionsWrapper.style.cssText = `
            display: grid;
            /* Adjusted grid: Col1 (Name/Dropdown), Col2 (Save/Load), Col3 (Delete) */
            /* Col1 width aims to leave space for Col2 to align with hex inputs */
            grid-template-columns: calc(238px - 8px) auto auto; /* 238px = 230px label + 8px gap. Subtract internal grid gap. */
            gap: 8px;
            align-items: center;
        `;

        // Name input (Row 1, Col 1)
        const newThemeNameInput = document.createElement('input');
        newThemeNameInput.type = 'text';
        newThemeNameInput.id = 'otk-custom-theme-name-input';
        newThemeNameInput.placeholder = 'Enter Theme Name';
        newThemeNameInput.style.cssText = "width: 100%; height: 25px; box-sizing: border-box; font-size: 12px; text-align: right;";
        // No explicit grid-column needed if it's the first element for the first cell

        // Save button (Row 1, Col 2)
        const saveThemeButton = document.createElement('button');
        saveThemeButton.id = 'otk-save-custom-theme-btn';
        saveThemeButton.textContent = 'Save Theme';
        saveThemeButton.style.cssText = "width: 100%; padding: 4px 8px; font-size: 11px; height: 25px; box-sizing: border-box; grid-column: 2 / 4;"; // Span columns 2 and 3
        // No explicit grid-column needed if it's the second element for the second cell --> This comment is now misleading, removing

        // Dropdown (Row 2, Col 1)
        const customThemesDropdown = document.createElement('select');
        customThemesDropdown.id = 'otk-custom-themes-dropdown';
        customThemesDropdown.style.cssText = "width: 100%; height: 25px; box-sizing: border-box; font-size: 12px; text-align: center; text-align-last: center;"; // Attempt to center-align
        // Needs explicit grid-column to go to the next row in the same column
        customThemesDropdown.style.gridColumn = '1 / 2';


        // Load button (Row 2, Col 2)
        const loadThemeButton = document.createElement('button');
        loadThemeButton.id = 'otk-load-custom-theme-btn';
        loadThemeButton.textContent = 'Load';
        loadThemeButton.style.cssText = "width: 100%; padding: 4px 8px; font-size: 11px; height: 25px; box-sizing: border-box;";
        loadThemeButton.style.gridColumn = '2 / 3';

        // Delete button (Row 2, Col 3 - or could be Row 1, Col 3 if preferred visually)
        // For simplicity, let's keep it with Load on Row 2 for now.
        const deleteThemeButton = document.createElement('button');
        deleteThemeButton.id = 'otk-delete-custom-theme-btn';
        deleteThemeButton.textContent = 'Delete';
        deleteThemeButton.style.cssText = "width: 100%; padding: 4px 8px; font-size: 11px; height: 25px; box-sizing: border-box; background-color: #803333; color: #ffffff;"; // Dark red, white text
        deleteThemeButton.onmouseover = () => deleteThemeButton.style.backgroundColor = '#a04444';
        deleteThemeButton.onmouseout = () => deleteThemeButton.style.backgroundColor = '#803333';
        deleteThemeButton.style.gridColumn = '3 / 4';

        // Append in order for grid flow
        customThemeActionsWrapper.appendChild(newThemeNameInput);    // R1 C1
        customThemeActionsWrapper.appendChild(saveThemeButton);      // R1 C2 (now spans C2-C3)
        // r1c3Placeholder is no longer needed as saveThemeButton spans its cell.
        // const r1c3Placeholder = document.createElement('div');
        // customThemeActionsWrapper.appendChild(r1c3Placeholder);

        customThemeActionsWrapper.appendChild(customThemesDropdown); // R2 C1
        customThemeActionsWrapper.appendChild(loadThemeButton);      // R2 C2
        customThemeActionsWrapper.appendChild(deleteThemeButton);    // R2 C3

        themeOptionsContainer.appendChild(customThemeActionsWrapper);

        const CUSTOM_THEMES_KEY = 'otkCustomThemes';

        saveThemeButton.addEventListener('click', () => {
            const themeName = newThemeNameInput.value.trim();
            if (!themeName) {
                alert("Please enter a name for the theme.");
                return;
            }

            let currentSettings = {};
            try {
                currentSettings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
            } catch (e) {
                consoleError("Error parsing theme settings from localStorage:", e);
            }
            let allCustomThemes = {};
            try {
                allCustomThemes = JSON.parse(localStorage.getItem(CUSTOM_THEMES_KEY)) || {};
            } catch (e) {
                consoleError("Error parsing custom themes from localStorage:", e);
            }
            allCustomThemes[themeName] = currentSettings;
            localStorage.setItem(CUSTOM_THEMES_KEY, JSON.stringify(allCustomThemes));

            alert(`Theme "${themeName}" saved!`);
            populateCustomThemesDropdown();
        });

        function populateCustomThemesDropdown() {
            const dropdown = document.getElementById('otk-custom-themes-dropdown');
            if (!dropdown) return;

            dropdown.innerHTML = ''; // Clear existing options

            // Add the "Revert to Active" / "Current Settings" option first
            const revertOption = document.createElement('option');
            revertOption.value = "__REVERT__"; // Special value
            revertOption.textContent = "‹ Active Settings ›"; // Display text
            dropdown.appendChild(revertOption);

            let customThemes = {};
            try {
                customThemes = JSON.parse(localStorage.getItem(CUSTOM_THEMES_KEY)) || {};
            } catch (e) {
                consoleError("Error parsing custom themes from localStorage:", e);
            }

            const themeNames = Object.keys(customThemes);

            if (themeNames.length === 0) {
                // If no custom themes, the "Revert" option might be confusing or lonely.
                // We can disable it or change its text, or simply let it be.
                // For now, let it be. User can save a theme to make the list more useful.
                // Alternatively, add a "No Saved Themes" disabled option after it.
                const noThemesOption = document.createElement('option');
                noThemesOption.textContent = "(No Saved Themes)";
                noThemesOption.disabled = true;
                dropdown.appendChild(noThemesOption);
            } else {
                themeNames.forEach(themeName => {
                    const option = document.createElement('option');
                    option.value = themeName; // Actual theme name
                    option.textContent = themeName;
                    dropdown.appendChild(option);
                });
            }
            dropdown.value = "__REVERT__"; // Ensure the revert option is selected by default
        }
        // Initial population of the dropdown when options window is set up
        populateCustomThemesDropdown();

        let prePreviewSettings = null; // To store settings before previewing a theme
        let currentlyPreviewingThemeName = null; // To track which theme is being previewed

        customThemesDropdown.addEventListener('change', () => {
            const selectedValue = customThemesDropdown.value;
            let customThemes = {};
            try {
                customThemes = JSON.parse(localStorage.getItem(CUSTOM_THEMES_KEY)) || {};
            } catch (e) {
                consoleError("Error parsing custom themes from localStorage:", e);
            }

            if (selectedValue === "__REVERT__") {
                if (prePreviewSettings) {
                    consoleLog("[PreviewTheme] Reverting to pre-preview settings.");
                    localStorage.setItem(THEME_SETTINGS_KEY, JSON.stringify(prePreviewSettings));
                    applyThemeSettings();
                    currentlyPreviewingThemeName = null;
                } else {
                    consoleLog("[PreviewTheme] 'Active Settings' selected. Ensuring current active settings are applied.");
                    const activeSettings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
                    localStorage.setItem(THEME_SETTINGS_KEY, JSON.stringify(activeSettings));
                    applyThemeSettings();
                    currentlyPreviewingThemeName = null;
                }
            } else {
                const themeToPreview = customThemes[selectedValue];
                if (themeToPreview) {
                    if (currentlyPreviewingThemeName === null) {
                        prePreviewSettings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
                        consoleLog("[PreviewTheme] Stored pre-preview settings:", JSON.parse(JSON.stringify(prePreviewSettings)));
                    }
                    consoleLog(`[PreviewTheme] Previewing theme "${selectedValue}". Settings:`, JSON.parse(JSON.stringify(themeToPreview)));
                    localStorage.setItem(THEME_SETTINGS_KEY, JSON.stringify(themeToPreview));
                    applyThemeSettings();
                    currentlyPreviewingThemeName = selectedValue;
                }
            }
        });

            loadThemeButton.addEventListener('click', () => {
                const selectedValue = customThemesDropdown.value;
                let customThemes = {};
                try {
                    customThemes = JSON.parse(localStorage.getItem(CUSTOM_THEMES_KEY)) || {};
                } catch (e) {
                    consoleError("Error parsing custom themes from localStorage:", e);
                }
                if (selectedValue && selectedValue !== '__REVERT__') {
                    const themeToLoad = customThemes[selectedValue];
                    if (themeToLoad) {
                        consoleLog(`[LoadTheme] Loading theme "${selectedValue}" and making it active.`);
                        localStorage.setItem(THEME_SETTINGS_KEY, JSON.stringify(themeToLoad));
                        applyThemeSettings(); // Apply and save
                        prePreviewSettings = null; // Clear pre-preview settings
                        currentlyPreviewingThemeName = null;
                        customThemesDropdown.value = '__REVERT__'; // Reset dropdown to the placeholder
                        alert(`Theme "${selectedValue}" loaded and saved as active.`);
                    }
                } else {
                    alert("Please select a theme to load.");
                }
            });

        deleteThemeButton.addEventListener('click', () => {
            const selectedValue = customThemesDropdown.value;
            if (selectedValue && selectedValue !== '__REVERT__') {
                if (confirm(`Are you sure you want to delete the theme "${selectedValue}"?`)) {
                    let customThemes = {};
                    try {
                        customThemes = JSON.parse(localStorage.getItem(CUSTOM_THEMES_KEY)) || {};
                    } catch (e) {
                        consoleError("Error parsing custom themes from localStorage:", e);
                    }
                    delete customThemes[selectedValue];
                    localStorage.setItem(CUSTOM_THEMES_KEY, JSON.stringify(customThemes));
                    populateCustomThemesDropdown();
                    alert(`Theme "${selectedValue}" deleted.`);
                }
            } else {
                alert("Please select a theme to delete.");
            }
        });


        // --- Reset All Button ---
        // It should be outside the normal flow of generated options, or the last item.
        // For now, let's re-add it manually after all generated content.
        const buttonWrapper = document.createElement('div');
        buttonWrapper.style.cssText = "display: flex; margin-top: 20px; width: 100%; gap: 8px;";

        const resetAllColorsButton = document.createElement('button');
        resetAllColorsButton.textContent = "Reset All Colors to Default";
        resetAllColorsButton.id = 'otk-reset-all-colors-btn'; // Keep ID if applyThemeSettings uses it
        resetAllColorsButton.style.cssText = "padding: 4px 8px; font-size: 11px; height: 25px; box-sizing: border-box; flex-grow: 1;";
        buttonWrapper.appendChild(resetAllColorsButton);

        const setAsMainThemeButton = document.createElement('button');
        setAsMainThemeButton.textContent = "Set as Main Theme";
        setAsMainThemeButton.id = 'otk-set-main-theme-btn';
        setAsMainThemeButton.style.cssText = "padding: 4px 8px; font-size: 11px; height: 25px; box-sizing: border-box; flex-grow: 1;";
        buttonWrapper.appendChild(setAsMainThemeButton);

        themeOptionsContainer.appendChild(buttonWrapper);

        setAsMainThemeButton.addEventListener('click', async () => {
            const currentSettings = localStorage.getItem(THEME_SETTINGS_KEY);
            if (currentSettings) {
                try {
                    await GM.setValue(MAIN_THEME_KEY, currentSettings);
                    alert("Current theme set as the main theme.");
                    consoleLog("Main theme saved to GM storage.");
                } catch (error) {
                    consoleError("Error saving main theme to GM storage:", error);
                    alert("Failed to set the main theme. See console for details.");
                }
            } else {
                alert("No theme settings to set as main.");
            }
        });

        // Helper function to get all theme configurations (used by save and reset)
        function getAllOptionConfigs() {
            // Note: labelText is not part of this config object, it's passed directly to createThemeOptionRow.
            // This function is primarily for mapping storageKey, cssVariable, defaultValue, inputType, etc.
            // The spelling change from "Color" to "Colour" happens in the createThemeOptionRow calls.
            return [
                { storageKey: 'guiBgColor', cssVariable: '--otk-gui-bg-color', defaultValue: '#181818', inputType: 'color', idSuffix: 'gui-bg' },
                { storageKey: 'titleTextColor', cssVariable: '--otk-title-text-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'title-text' },
                { storageKey: 'guiThreadListTitleColor', cssVariable: '--otk-gui-threadlist-title-color', defaultValue: '#e0e0e0', inputType: 'color', idSuffix: 'threadlist-title' },
                { storageKey: 'guiThreadListTimeColor', cssVariable: '--otk-gui-threadlist-time-color', defaultValue: '#FFD700', inputType: 'color', idSuffix: 'threadlist-time' },
                { storageKey: 'actualStatsTextColor', cssVariable: '--otk-stats-text-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'actual-stats-text' },
                { storageKey: 'statsDashColor', cssVariable: '--otk-stats-dash-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'stats-dash' },
                { storageKey: 'backgroundUpdatesStatsTextColor', cssVariable: '--otk-background-updates-stats-text-color', defaultValue: '#FFD700', inputType: 'color', idSuffix: 'background-updates-stats-text' },
                { storageKey: 'viewerBgColor', cssVariable: '--otk-viewer-bg-color', defaultValue: '#ffd1a4', inputType: 'color', idSuffix: 'viewer-bg' },
                { storageKey: 'guiBottomBorderColor', cssVariable: '--otk-gui-bottom-border-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'gui-bottom-border' },
                // Messages (Odds) - Corresponds to Depth 0, 2, 4...
                { storageKey: 'msgDepthOddContentFontSize', cssVariable: '--otk-msg-depth-odd-content-font-size', defaultValue: '16px', inputType: 'number', unit: 'px', min: 8, max: 24, idSuffix: 'msg-depth-odd-content-fontsize'},
                { storageKey: 'msgDepthOddBgColor', cssVariable: '--otk-msg-depth-odd-bg-color', defaultValue: '#ffffff', inputType: 'color', idSuffix: 'msg-depth-odd-bg' },
                { storageKey: 'msgDepthOddTextColor', cssVariable: '--otk-msg-depth-odd-text-color', defaultValue: '#333333', inputType: 'color', idSuffix: 'msg-depth-odd-text' },
                { storageKey: 'msgDepthOddHeaderTextColor', cssVariable: '--otk-msg-depth-odd-header-text-color', defaultValue: '#555555', inputType: 'color', idSuffix: 'msg-depth-odd-header-text' },
                { storageKey: 'viewerHeaderBorderColorOdd', cssVariable: '--otk-viewer-header-border-color-odd', defaultValue: '#000000', inputType: 'color', idSuffix: 'viewer-header-border-odd' },
                // Messages (Evens) - Corresponds to Depth 1, 3, 5...
                { storageKey: 'msgDepthEvenContentFontSize', cssVariable: '--otk-msg-depth-even-content-font-size', defaultValue: '16px', inputType: 'number', unit: 'px', min: 8, max: 24, idSuffix: 'msg-depth-even-content-fontsize'},
                { storageKey: 'msgDepthEvenBgColor', cssVariable: '--otk-msg-depth-even-bg-color', defaultValue: '#d9d9d9', inputType: 'color', idSuffix: 'msg-depth-even-bg' },
                { storageKey: 'msgDepthEvenTextColor', cssVariable: '--otk-msg-depth-even-text-color', defaultValue: '#333333', inputType: 'color', idSuffix: 'msg-depth-even-text' },
                { storageKey: 'msgDepthEvenHeaderTextColor', cssVariable: '--otk-msg-depth-even-header-text-color', defaultValue: '#555555', inputType: 'color', idSuffix: 'msg-depth-even-header-text' },
                { storageKey: 'cogIconColor', cssVariable: '--otk-cog-icon-color', defaultValue: '#FFD700', inputType: 'color', idSuffix: 'cog-icon' },
                { storageKey: 'disableBgFontColor', cssVariable: '--otk-disable-bg-font-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'disable-bg-font' },
                { storageKey: 'countdownBgColor', cssVariable: '--otk-countdown-bg-color', defaultValue: '#181818', inputType: 'color', idSuffix: 'countdown-bg' },
                { storageKey: 'countdownLabelTextColor', cssVariable: '--otk-countdown-label-text-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'countdown-label-text' },
                { storageKey: 'countdownTimerTextColor', cssVariable: '--otk-countdown-timer-text-color', defaultValue: '#ff8040', inputType: 'color', idSuffix: 'countdown-timer-text' },
                { storageKey: 'separatorColor', cssVariable: '--otk-separator-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'separator' },
                { storageKey: 'optionsTextColor', cssVariable: '--otk-options-text-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'options-text' },
                { storageKey: 'newMessagesDividerColor', cssVariable: '--otk-new-messages-divider-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'new-msg-divider' },
                { storageKey: 'newMessagesFontColor', cssVariable: '--otk-new-messages-font-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'new-msg-font' },
                { storageKey: 'newMessagesFontSize', cssVariable: '--otk-new-messages-font-size', defaultValue: '16px', inputType: 'number', unit: 'px', min: 8, max: 24, idSuffix: 'new-msg-font-size', requiresRerender: false },
                { storageKey: 'blockedContentFontColor', cssVariable: '--otk-blocked-content-font-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'blocked-content-font' },

                // Anchor Highlight Colors
                { storageKey: 'anchorHighlightBgColor', cssVariable: '--otk-anchor-highlight-bg-color', defaultValue: '#ffd1a4', inputType: 'color', idSuffix: 'anchor-bg' },
                { storageKey: 'anchorHighlightBorderColor', cssVariable: '--otk-anchor-highlight-border-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'anchor-border' },

                // '+' Icon Background
                { storageKey: 'plusIconBgColor', cssVariable: '--otk-plus-icon-bg-color', defaultValue: '#d9d9d9', inputType: 'color', idSuffix: 'plus-icon-bg-color' },

                // Icon Colors
                { storageKey: 'blurIconColor', cssVariable: '--otk-blur-icon-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'blur-icon' },
                { storageKey: 'blurIconBgColor', cssVariable: '--otk-blur-icon-bg-color', defaultValue: '#d9d9d9', inputType: 'color', idSuffix: 'blur-icon-bg' },
                { storageKey: 'resizeIconColor', cssVariable: '--otk-resize-icon-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'resize-icon' },
                { storageKey: 'resizeIconBgColor', cssVariable: '--otk-resize-icon-bg-color', defaultValue: '#d9d9d9', inputType: 'color', idSuffix: 'resize-icon-bg' },

                // GUI Button Colours
                { storageKey: 'guiButtonBgColor', cssVariable: '--otk-button-bg-color', defaultValue: '#555555', inputType: 'color', idSuffix: 'gui-button-bg' },
                { storageKey: 'guiButtonTextColor', cssVariable: '--otk-button-text-color', defaultValue: '#ffffff', inputType: 'color', idSuffix: 'gui-button-text' },
                { storageKey: 'guiButtonBorderColor', cssVariable: '--otk-button-border-color', defaultValue: '#777777', inputType: 'color', idSuffix: 'gui-button-border' },
                { storageKey: 'guiButtonHoverBgColor', cssVariable: '--otk-button-hover-bg-color', defaultValue: '#666666', inputType: 'color', idSuffix: 'gui-button-hover-bg' },
                { storageKey: 'guiButtonActiveBgColor', cssVariable: '--otk-button-active-bg-color', defaultValue: '#444444', inputType: 'color', idSuffix: 'gui-button-active-bg' },

                // Loading Screen Colours
                { storageKey: 'loadingOverlayBaseHexColor', cssVariable: '--otk-loading-overlay-base-hex-color', defaultValue: '#000000', inputType: 'color', idSuffix: 'loading-overlay-base-hex' },
                { storageKey: 'loadingOverlayOpacity', cssVariable: '--otk-loading-overlay-opacity', defaultValue: '1', inputType: 'number', unit: null, min:0.0, max:1.0, step:0.05, idSuffix: 'loading-overlay-opacity' },
                { storageKey: 'loadingTextColor', cssVariable: '--otk-loading-text-color', defaultValue: '#ffffff', inputType: 'color', idSuffix: 'loading-text' },
                { storageKey: 'loadingProgressBarBgColor', cssVariable: '--otk-loading-progress-bar-bg-color', defaultValue: '#333333', inputType: 'color', idSuffix: 'loading-progress-bg' },
                { storageKey: 'loadingProgressBarFillColor', cssVariable: '--otk-loading-progress-bar-fill-color', defaultValue: '#4CAF50', inputType: 'color', idSuffix: 'loading-progress-fill' },
                { storageKey: 'loadingProgressBarTextColor', cssVariable: '--otk-loading-progress-bar-text-color', defaultValue: '#ffffff', inputType: 'color', idSuffix: 'loading-progress-text' },

                // Clock Colours
                { storageKey: 'clockBgColor', cssVariable: '--otk-clock-bg-color', defaultValue: '#181818', inputType: 'color', idSuffix: 'clock-bg' },
                { storageKey: 'clockTextColor', cssVariable: '--otk-clock-text-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'clock-text' },
                { storageKey: 'clockBorderColor', cssVariable: '--otk-clock-border-color', defaultValue: '#181818', inputType: 'color', idSuffix: 'clock-border' },
                { storageKey: 'clockSearchBgColor', cssVariable: '--otk-clock-search-bg-color', defaultValue: '#333', inputType: 'color', idSuffix: 'clock-search-bg' },
                { storageKey: 'clockCogColor', cssVariable: '--otk-clock-cog-color', defaultValue: '#FFD700', inputType: 'color', idSuffix: 'clock-cog' },
                { storageKey: 'clockSearchTextColor', cssVariable: '--otk-clock-search-text-color', defaultValue: '#e6e6e6', inputType: 'color', idSuffix: 'clock-search-text' }
            ];
        }

        function resetAllThemeSettingsToDefault(promptUser = true) {
            if (promptUser && !confirm("Are you sure you want to reset all theme settings to their defaults?")) {
                return;
            }

            consoleLog("Resetting all theme settings to default...");
            // Clear the active theme settings from localStorage.
            localStorage.removeItem(THEME_SETTINGS_KEY);

            const allOptionConfigs = getAllOptionConfigs();

            allOptionConfigs.forEach(opt => {
                const defaultValue = opt.defaultValue;
                // Set the CSS variable to the default value.
                if (opt.cssVariable) {
                    document.documentElement.style.setProperty(opt.cssVariable, defaultValue);
                }

                // Update the input fields in the options panel to reflect the default values.
                const mainInput = document.getElementById(`otk-${opt.idSuffix}`);
                const hexInput = opt.inputType === 'color' ? document.getElementById(`otk-${opt.idSuffix}-hex`) : null;

                let displayValue = defaultValue;
                if (opt.unit && displayValue.endsWith(opt.unit)) {
                    displayValue = displayValue.replace(opt.unit, '');
                }

                if (mainInput) mainInput.value = displayValue;
                if (hexInput) hexInput.value = displayValue;

                if (opt.storageKey === 'cogIconColor') {
                    const cogIcon = document.getElementById('otk-settings-cog');
                    if (cogIcon) cogIcon.style.color = defaultValue;
                }
            });

            const newBooleanSettings = [
                { key: 'otkMsgDepthOddDisableHeaderUnderline', defaultValue: false, idSuffix: 'msg-depth-odd-disable-header-underline' },
                { key: 'otkMsgDepthEvenDisableHeaderUnderline', defaultValue: true, idSuffix: 'msg-depth-even-disable-header-underline' },
                { key: 'showOddMessageFilename', defaultValue: false, idSuffix: 'show-odd-filename'},
                { key: 'showEvenMessageFilename', defaultValue: false, idSuffix: 'show-even-filename'}
            ];
            newBooleanSettings.forEach(opt => {
                const checkbox = document.getElementById(`otk-${opt.idSuffix}-checkbox`);
                if (checkbox) {
                    checkbox.checked = opt.defaultValue;
                }
            });

            // The applyThemeSettings() call is no longer needed here if called by the initiator.
            // If called from the reset button, it should call it.
            // Let's call it for the standalone reset case.
            if (promptUser) {
                // No need to call applyThemeSettings() as we have manually set all the properties.
                // Calling it might re-apply old settings from memory before a refresh.
                forceViewerRerenderAfterThemeChange(); // Force a re-render if the viewer is open.
                alert("All theme settings have been reset to their defaults.");
            }
        }

        resetAllColorsButton.addEventListener('click', () => {
            resetAllThemeSettingsToDefault(true); // true to prompt user
        });

        // Event Listeners for cog and close
        const cogIcon = document.getElementById('otk-settings-cog');
        if (cogIcon) {
            cogIcon.addEventListener('click', () => {
                optionsWindow.style.display = optionsWindow.style.display === 'none' ? 'flex' : 'none';
                        consoleLog("Toggled options window visibility to:", optionsWindow.style.display);
            });
        } else {
                    consoleError("Cog icon not found for options window toggle.");
        }

        closeButton.addEventListener('click', () => {
            // Reversion logic for theme preview
            if (prePreviewSettings) {
                consoleLog("[OptionsClose] Reverting to pre-preview settings as options window is closing.");
                localStorage.setItem(THEME_SETTINGS_KEY, JSON.stringify(prePreviewSettings));
                applyThemeSettings(); // Apply the restored settings

                prePreviewSettings = null; // Clear the stored pre-preview settings
                currentlyPreviewingThemeName = null; // Clear the currently previewing theme name

                // Reset dropdown to "Active Settings"
                const dropdown = document.getElementById('otk-custom-themes-dropdown');
                if (dropdown) {
                    dropdown.value = "__REVERT__";
                }
            } else {
                consoleLog("[OptionsClose] No active preview to revert. Closing options window.");
            }

            optionsWindow.style.display = 'none';
            consoleLog("Options window closed.");
        });

        // Make window draggable
        let isOptionsDragging = false;
        let optionsOffsetX, optionsOffsetY;

        titleBar.addEventListener('mousedown', (e) => {
            // Prevent dragging if clicking on the close button itself
            if (e.target === closeButton || closeButton.contains(e.target) || e.target.tagName === 'BUTTON') {
                return;
            }
            isOptionsDragging = true;
            optionsOffsetX = e.clientX - optionsWindow.offsetLeft;
            optionsOffsetY = e.clientY - optionsWindow.offsetTop;
            titleBar.style.userSelect = 'none'; // Prevent text selection during drag
            document.body.style.userSelect = 'none'; // Prevent text selection on body during drag
            consoleLog("Draggable window: mousedown");
        });

        document.addEventListener('mousemove', (e) => {
            if (isOptionsDragging) {
                let newLeft = e.clientX - optionsOffsetX;
                let newTop = e.clientY - optionsOffsetY;

                optionsWindow.style.left = newLeft + 'px';
                optionsWindow.style.top = newTop + 'px';
            }
        });

        document.addEventListener('mouseup', () => {
            if (isOptionsDragging) {
                isOptionsDragging = false;
                titleBar.style.userSelect = ''; // Re-enable text selection
                document.body.style.userSelect = '';
                consoleLog("Draggable window: mouseup");
                // Future: save position to localStorage here if desired
                // localStorage.setItem('otkOptionsWindowPos', JSON.stringify({top: optionsWindow.style.top, left: optionsWindow.style.left}));
            }
        });

        consoleLog("Options Window setup complete with drag functionality.");
    }

function renderFilterEditorView(ruleToEdit = null) {
    const rightContent = document.getElementById('otk-filter-content');
    if (!rightContent) return;

    rightContent.innerHTML = ''; // Clear previous content

    const allRules = JSON.parse(localStorage.getItem(FILTER_RULES_V2_KEY) || '[]');
    const isEditing = ruleToEdit ? allRules.some(r => r.id === ruleToEdit.id) : false;

    const rule = ruleToEdit || {
        id: Date.now(),
        category: 'keyword',
        action: 'filterOut',
        matchContent: '',
        replaceContent: '',
        enabled: true
    };

    const form = document.createElement('div');
    form.style.cssText = 'display: flex; flex-direction: column; gap: 10px; height: 100%;';

    // Helper to create a labeled row
    const createRow = (labelText, ...elements) => {
        const row = document.createElement('div');
        row.style.cssText = 'display: flex; align-items: center; gap: 10px;';
        const label = document.createElement('label');
        label.textContent = labelText;
        label.style.width = '120px';
        label.style.flexShrink = '0';
        row.appendChild(label);
        elements.forEach(el => row.appendChild(el));
        return row;
    };

    // Category Dropdown
    const categorySelect = document.createElement('select');
    categorySelect.style.flexGrow = '1';
    const categories = [
        { value: 'keyword', text: 'Keyword/Text' },
        { value: 'embeddedLink', text: 'Embedded Link' },
        { value: 'attachedMedia', text: 'Attached Media' },
        { value: 'entireMessage', text: 'Entire Message' }
    ];
    categories.forEach(cat => {
        const option = document.createElement('option');
        option.value = cat.value;
        option.textContent = cat.text;
        categorySelect.appendChild(option);
    });
    categorySelect.value = rule.category;
    form.appendChild(createRow('Category:', categorySelect));

    // Action Dropdown
    const actionSelect = document.createElement('select');
    actionSelect.style.flexGrow = '1';
    const actions = [
        { value: 'filterOut', text: 'Filter out entire message' },
        { value: 'remove', text: 'Remove matching content only' },
        { value: 'replace', text: 'Replace matching content' }
    ];
    actions.forEach(act => {
        const option = document.createElement('option');
        option.value = act.value;
        option.textContent = act.text;
        actionSelect.appendChild(option);
    });
    actionSelect.value = rule.action;
    form.appendChild(createRow('Action:', actionSelect));

    // Match Content Input
    const matchContentRow = createRow('Match Content:', document.createElement('textarea'));
    const matchContentInput = matchContentRow.querySelector('textarea');
    matchContentInput.placeholder = 'Content to match...';
    matchContentInput.value = rule.matchContent;

    // Make this row and its textarea grow to fill available space
    matchContentRow.style.flexGrow = '1';
    matchContentRow.style.alignItems = 'stretch';
    matchContentInput.style.cssText = 'flex-grow: 1; width: 100%; box-sizing: border-box; resize: vertical; height: 100%;';
    form.appendChild(matchContentRow);

    // Replace Content Input (conditionally displayed)
    const replaceContentRow = createRow('Replace With:', document.createElement('textarea'));
    const replaceContentInput = replaceContentRow.querySelector('textarea');
    replaceContentInput.placeholder = 'Replacement content...';
    replaceContentInput.style.cssText = 'flex-grow: 1; width: 100%; box-sizing: border-box; resize: vertical; height: 60px;';
    replaceContentInput.value = rule.replaceContent;
    form.appendChild(replaceContentRow);

    const toggleReplaceRow = () => {
        replaceContentRow.style.display = actionSelect.value === 'replace' ? 'flex' : 'none';
    };
    actionSelect.addEventListener('change', toggleReplaceRow);
    toggleReplaceRow(); // Initial check

    const saveRuleLogic = () => {
        const newRuleData = {
            id: rule.id,
            category: categorySelect.value,
            action: actionSelect.value,
            matchContent: matchContentInput.value.trim(),
            replaceContent: replaceContentInput.value.trim(),
            enabled: rule.enabled
        };

        if (!newRuleData.matchContent) {
            alert('Match Content cannot be empty.');
            return false;
        }

        let currentRules = JSON.parse(localStorage.getItem(FILTER_RULES_V2_KEY) || '[]');
        const ruleIndex = currentRules.findIndex(r => r.id === rule.id);

        if (ruleIndex > -1) {
            currentRules[ruleIndex] = newRuleData;
        } else {
            currentRules.push(newRuleData);
        }
        localStorage.setItem(FILTER_RULES_V2_KEY, JSON.stringify(currentRules));
        return true;
    };

    // Buttons
    const buttonContainer = document.createElement('div');
    buttonContainer.style.cssText = 'display: flex; justify-content: flex-end; gap: 10px; margin-top: auto;';

    const saveBtn = createTrackerButton(isEditing ? 'Save Changes' : 'Create Filter');
    saveBtn.addEventListener('click', () => {
        if (saveRuleLogic()) {
            renderFilterList();
        }
    });

    const cancelBtn = createTrackerButton('Cancel');
    cancelBtn.addEventListener('click', () => {
        renderFilterList();
    });

    const saveAndCloseBtn = createTrackerButton(isEditing ? 'Save and Close' : 'Create Filter and Close');
    saveAndCloseBtn.addEventListener('click', () => {
        if (saveRuleLogic()) {
            document.getElementById('otk-filter-window').style.display = 'none';
        }
    });

    buttonContainer.appendChild(cancelBtn);
    buttonContainer.appendChild(saveBtn);
    buttonContainer.appendChild(saveAndCloseBtn);
    form.appendChild(buttonContainer);

    rightContent.appendChild(form);
}
function renderFilterList() {
    const rightContent = document.getElementById('otk-filter-content');
    if (!rightContent) return;
    rightContent.innerHTML = ''; // Clear previous content

    const header = document.createElement('div');
    header.style.cssText = 'display: flex; justify-content: space-between; align-items: center; margin-bottom: 10px; padding-right: 15px;'; // Add padding for scrollbar

    const checkAllContainer = document.createElement('div');
    checkAllContainer.style.cssText = 'display: flex; align-items: center;';
    const checkAllBox = document.createElement('input');
    checkAllBox.type = 'checkbox';
    checkAllBox.id = 'otk-filter-select-all';
    const checkAllLabel = document.createElement('label');
    checkAllLabel.textContent = 'Select All';
    checkAllLabel.htmlFor = 'otk-filter-select-all';
    checkAllLabel.style.marginLeft = '5px';

    checkAllContainer.appendChild(checkAllBox);
    checkAllContainer.appendChild(checkAllLabel);
    header.appendChild(checkAllContainer);

    const buttonGroup = document.createElement('div');
    buttonGroup.style.cssText = 'display: flex; gap: 10px;';

    const editSelectedBtn = createTrackerButton('Edit Selected');
    editSelectedBtn.id = 'otk-edit-selected-filter-btn';
    editSelectedBtn.style.display = 'none';
    buttonGroup.appendChild(editSelectedBtn);

    const deleteSelectedBtn = createTrackerButton('Delete Selected');
    deleteSelectedBtn.id = 'otk-delete-selected-filters-btn';
    deleteSelectedBtn.style.display = 'none';
    buttonGroup.appendChild(deleteSelectedBtn);

    header.appendChild(buttonGroup);

    rightContent.appendChild(header);

    const ruleListContainer = document.createElement('div');
    ruleListContainer.id = 'otk-filter-rule-list-container';
    ruleListContainer.style.cssText = 'display: flex; flex-direction: column; max-height: 280px; overflow-y: auto; padding-right: 15px;';
    rightContent.appendChild(ruleListContainer);

    const rules = JSON.parse(localStorage.getItem(FILTER_RULES_V2_KEY) || '[]');
    if (rules.length === 0) {
        ruleListContainer.textContent = 'No filter rules saved.';
        return;
    }

    const categoryDisplayMap = {
        keyword: 'Keyword',
        embeddedLink: 'Link',
        attachedMedia: 'Media',
        entireMessage: 'Message'
    };

    const actionDisplayMap = {
        filterOut: 'Filter Out',
        remove: 'Remove',
        replace: 'Replace'
    };

    rules.forEach((rule, index) => {
        const ruleDiv = document.createElement('div');
        ruleDiv.style.cssText = `
            display: grid;
            grid-template-columns: auto 1fr auto;
            align-items: center;
            gap: 10px;
            padding: 10px;
            border-top: 1px solid #444;
            background-color: ${rule.enabled ? '#3a3a3a' : '#2a2a2a'};
        `;

        const checkbox = document.createElement('input');
        checkbox.type = 'checkbox';
        checkbox.dataset.ruleId = rule.id;
        ruleDiv.appendChild(checkbox);

        const mainContentDiv = document.createElement('div');
        mainContentDiv.style.cssText = 'display: flex; flex-direction: column; gap: 5px; overflow: hidden;';

        const headerDiv = document.createElement('div');
        headerDiv.style.cssText = 'display: flex; align-items: center; gap: 10px;';

        const title = document.createElement('h5');
        const categoryStr = categoryDisplayMap[rule.category] || rule.category;
        const actionStr = actionDisplayMap[rule.action] || rule.action;
        title.textContent = `Filter #${index + 1} (${categoryStr}, ${actionStr})`;
        title.style.cssText = 'margin: 0; font-size: 14px; color: #f0f0f0;';

        headerDiv.appendChild(title);
        mainContentDiv.appendChild(headerDiv);

        const matchContentDiv = document.createElement('div');
        matchContentDiv.style.whiteSpace = 'nowrap';
        matchContentDiv.style.overflow = 'hidden';
        matchContentDiv.style.textOverflow = 'ellipsis';
        matchContentDiv.title = rule.matchContent;

        const strongEl = document.createElement('strong');
        strongEl.textContent = 'Match: ';
        matchContentDiv.appendChild(strongEl);

        const codeSpan = document.createElement('span');
        codeSpan.style.fontFamily = 'monospace';
        codeSpan.style.padding = '2px 4px';
        codeSpan.style.borderRadius = '3px';

        let mediaHashForPopup = null;
        let hoverTarget = null;

        if (rule.category === 'attachedMedia') {
            mediaHashForPopup = rule.matchContent.replace('md5:', '');
            codeSpan.textContent = rule.matchContent;
            hoverTarget = codeSpan;
        } else if (rule.category === 'entireMessage') {
            try {
                const conditions = JSON.parse(rule.matchContent);
                if (conditions.media) {
                    mediaHashForPopup = conditions.media.replace('md5:', '');
                    const mediaValue = conditions.media;
                    const textBefore = rule.matchContent.substring(0, rule.matchContent.indexOf(mediaValue));
                    const textAfter = rule.matchContent.substring(rule.matchContent.indexOf(mediaValue) + mediaValue.length);

                    codeSpan.appendChild(document.createTextNode(textBefore));
                    const hashSpan = document.createElement('span');
                    hashSpan.className = 'otk-media-hash-preview';
                    hashSpan.textContent = mediaValue;
                    hashSpan.style.textDecoration = 'underline';
                    hashSpan.style.cursor = 'pointer';
                    codeSpan.appendChild(hashSpan);
                    codeSpan.appendChild(document.createTextNode(textAfter));
                    hoverTarget = hashSpan;
                } else {
                    codeSpan.textContent = rule.matchContent;
                }
            } catch (e) {
                codeSpan.textContent = rule.matchContent;
            }
        } else {
            codeSpan.textContent = rule.matchContent;
        }

        matchContentDiv.appendChild(codeSpan);
        mainContentDiv.appendChild(matchContentDiv);

        if (hoverTarget && mediaHashForPopup) {
            let thumbnailPopup = null;
            let blobUrl = null;

            const hideThumbnail = () => {
                if (thumbnailPopup) {
                    thumbnailPopup.remove();
                    thumbnailPopup = null;
                }
                if (blobUrl) {
                    URL.revokeObjectURL(blobUrl);
                    blobUrl = null;
                }
            };

            hoverTarget.addEventListener('mouseenter', (e) => {
                hideThumbnail();
                if (!otkMediaDB) return;
                const thumbKey = `${mediaHashForPopup}_thumb`;

                const transaction = otkMediaDB.transaction(['mediaStore'], 'readonly');
                const store = transaction.objectStore('mediaStore');
                const request = store.get(thumbKey);

                request.onsuccess = (event) => {
                    const storedItem = event.target.result;
                    thumbnailPopup = document.createElement('div');
                    thumbnailPopup.id = 'otk-thumbnail-popup';
                    thumbnailPopup.style.cssText = `
                        position: fixed; z-index: 10005; background: #1a1a1a;
                        border: 1px solid #555; border-radius: 3px; padding: 5px;
                        pointer-events: none; max-width: 250px; max-height: 250px;
                    `;
                    if (storedItem && storedItem.blob) {
                        blobUrl = URL.createObjectURL(storedItem.blob);
                        const img = document.createElement('img');
                        img.src = blobUrl;
                        img.style.cssText = 'max-width: 100%; max-height: 100%; display: block;';
                        thumbnailPopup.appendChild(img);
                    } else {
                        thumbnailPopup.textContent = 'Thumbnail not in cache';
                        thumbnailPopup.style.color = '#ccc';
                        thumbnailPopup.style.fontSize = '12px';
                    }
                    document.body.appendChild(thumbnailPopup);
                    thumbnailPopup.style.left = `${e.clientX + 15}px`;
                    thumbnailPopup.style.top = `${e.clientY + 15}px`;
                };
                request.onerror = (event) => consoleError("Error fetching thumbnail for popup:", event.target.error);
            });

            hoverTarget.addEventListener('mouseleave', hideThumbnail);
        }

        if (rule.action === 'replace') {
            const replaceContentDiv = document.createElement('div');
            replaceContentDiv.innerHTML = `<strong>Replace:</strong> <span style="font-family: monospace; padding: 2px 4px; border-radius: 3px;"></span>`;
            replaceContentDiv.querySelector('span').textContent = rule.replaceContent;
            replaceContentDiv.style.whiteSpace = 'nowrap';
            replaceContentDiv.style.overflow = 'hidden';
            replaceContentDiv.style.textOverflow = 'ellipsis';
            replaceContentDiv.title = rule.replaceContent;
            mainContentDiv.appendChild(replaceContentDiv);
        }

        ruleDiv.appendChild(mainContentDiv);

        const toggleSwitch = document.createElement('label');
        toggleSwitch.className = 'otk-switch';
        const toggleInput = document.createElement('input');
        toggleInput.type = 'checkbox';
        toggleInput.checked = rule.enabled;
        toggleInput.addEventListener('change', () => {
            rule.enabled = toggleInput.checked;
            const updatedRules = JSON.parse(localStorage.getItem(FILTER_RULES_V2_KEY) || '[]');
            const ruleIndex = updatedRules.findIndex(r => r.id === rule.id);
            if (ruleIndex > -1) {
                updatedRules[ruleIndex].enabled = rule.enabled;
                localStorage.setItem(FILTER_RULES_V2_KEY, JSON.stringify(updatedRules));
                ruleDiv.style.backgroundColor = rule.enabled ? '#3a3a3a' : '#2a2a2a';
            }
        });
        const toggleSlider = document.createElement('span');
        toggleSlider.className = 'otk-slider round';
        toggleSwitch.appendChild(toggleInput);
        toggleSwitch.appendChild(toggleSlider);
        ruleDiv.appendChild(toggleSwitch);

        ruleListContainer.appendChild(ruleDiv);
    });

    const checkboxes = Array.from(ruleListContainer.querySelectorAll('input[type="checkbox"][data-rule-id]'));

    const updateBulkActionButtons = () => {
        const checkedCount = checkboxes.filter(cb => cb.checked).length;
        deleteSelectedBtn.style.display = checkedCount > 0 ? 'inline-block' : 'none';
        editSelectedBtn.style.display = checkedCount === 1 ? 'inline-block' : 'none';

        const allChecked = checkboxes.every(cb => cb.checked);
        checkAllBox.checked = checkboxes.length > 0 && allChecked;
    };

    checkboxes.forEach(cb => cb.addEventListener('change', updateBulkActionButtons));

    checkAllBox.addEventListener('change', () => {
        checkboxes.forEach(cb => cb.checked = checkAllBox.checked);
        updateBulkActionButtons();
    });

    deleteSelectedBtn.addEventListener('click', () => {
        if (!confirm('Are you sure you want to delete the selected rules?')) return;
        let currentRules = JSON.parse(localStorage.getItem(FILTER_RULES_V2_KEY) || '[]');
        const idsToDelete = new Set(checkboxes.filter(cb => cb.checked).map(cb => parseInt(cb.dataset.ruleId, 10)));
        const newRules = currentRules.filter(rule => !idsToDelete.has(rule.id));
        localStorage.setItem(FILTER_RULES_V2_KEY, JSON.stringify(newRules));
        renderFilterList();
    });

    editSelectedBtn.addEventListener('click', () => {
        const selectedCheckbox = checkboxes.find(cb => cb.checked);
        if (selectedCheckbox) {
            const ruleId = parseInt(selectedCheckbox.dataset.ruleId, 10);
            const ruleToEdit = rules.find(r => r.id === ruleId);
            if (ruleToEdit) {
                renderFilterEditorView(ruleToEdit);
            }
        }
    });

    if (!document.getElementById('otk-switch-styles')) {
        const style = document.createElement('style');
        style.id = 'otk-switch-styles';
        style.innerHTML = `
            .otk-switch { position: relative; display: inline-block; width: 34px; height: 20px; }
            .otk-switch input { opacity: 0; width: 0; height: 0; }
            .otk-slider { position: absolute; cursor: pointer; top: 0; left: 0; right: 0; bottom: 0; background-color: #ccc; transition: .4s; }
            .otk-slider:before { position: absolute; content: ""; height: 12px; width: 12px; left: 4px; bottom: 4px; background-color: white; transition: .4s; }
            input:checked + .otk-slider { background-color: #4CAF50; }
            input:focus + .otk-slider { box-shadow: 0 0 1px #4CAF50; }
            input:checked + .otk-slider:before { transform: translateX(14px); }
            .otk-slider.round { border-radius: 20px; }
            .otk-slider.round:before { border-radius: 50%; }
        `;
        document.head.appendChild(style);
    }
}

function setupFilterWindow() {
    consoleLog("Setting up Filter Window...");

    if (document.getElementById('otk-filter-window')) {
        consoleLog("Filter window already exists.");
        return;
    }

    const filterWindow = document.createElement('div');
    filterWindow.id = 'otk-filter-window';
    filterWindow.style.cssText = `
        position: fixed;
        top: 120px;
        left: 120px;
        width: 900px;
        height: 400px;
        background-color: #2c2c2c;
        border: 1px solid #444;
        border-radius: 5px;
        z-index: 10001;
        display: none;
        flex-direction: column;
        box-shadow: 0 5px 15px rgba(0,0,0,0.5);
        color: var(--otk-options-text-color);
    `;

    const titleBar = document.createElement('div');
    titleBar.style.cssText = `
        padding: 8px 12px;
        background-color: #383838;
        color: #f0f0f0;
        font-weight: bold;
        cursor: move;
        border-bottom: 1px solid #444;
        border-top-left-radius: 5px;
        border-top-right-radius: 5px;
        display: flex;
        justify-content: space-between;
        align-items: center;
    `;
    titleBar.textContent = 'Filter Settings';

    const closeButton = document.createElement('span');
    closeButton.innerHTML = '&#x2715;';
    closeButton.style.cssText = 'cursor: pointer; font-size: 16px;';
    closeButton.addEventListener('click', () => {
        filterWindow.style.display = 'none';
    });

    titleBar.appendChild(closeButton);
    filterWindow.appendChild(titleBar);

    let isDragging = false;
    let offsetX, offsetY;

    titleBar.addEventListener('mousedown', (e) => {
        if (e.target === closeButton) return;
        isDragging = true;
        offsetX = e.clientX - filterWindow.offsetLeft;
        offsetY = e.clientY - filterWindow.offsetTop;
        titleBar.style.userSelect = 'none';
        document.body.style.userSelect = 'none';
    });

    document.addEventListener('mousemove', (e) => {
        if (isDragging) {
            filterWindow.style.left = `${e.clientX - offsetX}px`;
            filterWindow.style.top = `${e.clientY - offsetY}px`;
        }
    });

    document.addEventListener('mouseup', () => {
        isDragging = false;
        titleBar.style.userSelect = '';
        document.body.style.userSelect = '';
    });

    const mainContent = document.createElement('div');
    mainContent.style.cssText = 'display: flex; flex-grow: 1;';
    filterWindow.appendChild(mainContent);

    const leftMenu = document.createElement('div');
    leftMenu.id = 'otk-filter-menu';
    leftMenu.style.cssText = `
        width: 120px;
        padding: 10px;
        border-right: 1px solid #444;
        display: flex;
        flex-direction: column;
        gap: 10px;
    `;
    mainContent.appendChild(leftMenu);

    const rightContent = document.createElement('div');
    rightContent.id = 'otk-filter-content';
    rightContent.style.cssText = 'padding: 10px; flex-grow: 1; display: flex; flex-direction: column;';
    mainContent.appendChild(rightContent);

    // ... (rest of the setupFilterWindow code remains unchanged, including the titleBar, closeButton, mainContent, leftMenu, rightContent, dragging logic, etc.)

    const filterListBtn = createTrackerButton('Filter List');
    filterListBtn.addEventListener('click', renderFilterList);
    leftMenu.appendChild(filterListBtn);

    const newFilterBtn = createTrackerButton('New Filter');
    newFilterBtn.addEventListener('click', () => renderFilterEditorView());
    leftMenu.appendChild(newFilterBtn);

    const closeMenuBtn = createTrackerButton('Close');
    closeMenuBtn.addEventListener('click', () => {
        filterWindow.style.display = 'none';
    });
    leftMenu.appendChild(closeMenuBtn);

    document.body.appendChild(filterWindow);
    consoleLog("Filter Window setup complete.");
}



function setupClockOptionsWindow() {
    consoleLog("Setting up Clock Options Window...");

    if (document.getElementById('otk-clock-options-window')) {
        consoleLog("Clock Options window already exists.");
        return;
    }

    const clockOptionsWindow = document.createElement('div');
    clockOptionsWindow.id = 'otk-clock-options-window';
    clockOptionsWindow.style.cssText = `
        position: fixed;
        top: 150px;
        left: 150px;
        width: 350px;
        min-height: 150px;
        max-height: 400px;
        background-color: #2c2c2c;
        border: 1px solid #444;
        border-radius: 5px;
        z-index: 10001; /* Above main options window */
        display: none;
        flex-direction: column;
        box-shadow: 0 5px 15px rgba(0,0,0,0.5);
        color: var(--otk-options-text-color);
    `;

    const titleBar = document.createElement('div');
    titleBar.id = 'otk-clock-options-title-bar';
    titleBar.style.cssText = `
        padding: 8px 12px;
        background-color: #383838;
        color: #f0f0f0;
        font-weight: bold;
        cursor: move;
        border-bottom: 1px solid #444;
        border-top-left-radius: 5px;
        border-top-right-radius: 5px;
        display: flex;
        justify-content: space-between;
        align-items: center;
    `;
    titleBar.textContent = 'Clock Options';

    const closeButton = document.createElement('span');
    closeButton.id = 'otk-clock-options-close-btn';
    closeButton.innerHTML = '&#x2715;';
    closeButton.style.cssText = `
        cursor: pointer;
        font-size: 16px;
        padding: 0 5px;
    `;
    closeButton.title = "Close Clock Settings";

    closeButton.addEventListener('click', () => {
        clockOptionsWindow.style.display = 'none';
    });

    titleBar.appendChild(closeButton);
    clockOptionsWindow.appendChild(titleBar);

    const contentArea = document.createElement('div');
    contentArea.id = 'otk-clock-options-content';
    contentArea.style.cssText = `
        padding: 15px;
        flex-grow: 1;
        overflow-y: auto;
    `;
    clockOptionsWindow.appendChild(contentArea);

    document.body.appendChild(clockOptionsWindow);

    // Make window draggable
    let isDragging = false;
    let offsetX, offsetY;

    titleBar.addEventListener('mousedown', (e) => {
        if (e.target === closeButton) return;
        isDragging = true;
        offsetX = e.clientX - clockOptionsWindow.offsetLeft;
        offsetY = e.clientY - clockOptionsWindow.offsetTop;
        titleBar.style.userSelect = 'none';
        document.body.style.userSelect = 'none';
    });

    document.addEventListener('mousemove', (e) => {
        if (isDragging) {
            let newLeft = e.clientX - offsetX;
            let newTop = e.clientY - offsetY;
            clockOptionsWindow.style.left = newLeft + 'px';
            clockOptionsWindow.style.top = newTop + 'px';
        }
    });

    document.addEventListener('mouseup', () => {
        if (isDragging) {
            isDragging = false;
            titleBar.style.userSelect = '';
            document.body.style.userSelect = '';
        }
    });
}

    // --- Initial Actions / Main Execution ---
    async function main() {
        // Migration: Remove old filter rules key if it exists
        if (localStorage.getItem('otkFilterRules')) {
            localStorage.removeItem('otkFilterRules');
            consoleLog('[Migration] Removed outdated otkFilterRules from localStorage.');
        }

        // Clock data migration
        if (!localStorage.getItem('otkClocks')) {
            const oldTimezone = localStorage.getItem('otkClockTimezone');
            const oldDisplayPlace = localStorage.getItem('otkClockDisplayPlace');
            let initialClocks = [];
            if (oldTimezone) {
                initialClocks.push({
                    id: Date.now(),
                    timezone: oldTimezone,
                    displayPlace: oldDisplayPlace || oldTimezone.split('/').pop().replace(/_/g, ' ')
                });
            } else {
                // Default clock if no old settings exist
                initialClocks.push({
                    id: Date.now(),
                    timezone: 'America/Chicago',
                    displayPlace: 'Chicago'
                });
            }
            localStorage.setItem('otkClocks', JSON.stringify(initialClocks));
            consoleLog('Clock settings migrated to new multi-clock format.');
        }

        consoleLog("Starting OTK Thread Tracker script (v2.8)...");

        try {
            const storedBlurred = JSON.parse(localStorage.getItem(BLURRED_IMAGES_KEY));
            if (Array.isArray(storedBlurred)) {
                blurredImages = new Set(storedBlurred);
            }
            consoleLog(`Loaded ${blurredImages.size} blurred image hashes.`);
        } catch (e) {
            consoleError("Error parsing blurred images from localStorage:", e);
            blurredImages = new Set();
        }

        try {
            const storedBlocked = JSON.parse(localStorage.getItem(BLOCKED_THREADS_KEY));
            if (Array.isArray(storedBlocked)) {
                blockedThreads = new Set(storedBlocked);
            }
            consoleLog(`Loaded ${blockedThreads.size} blocked thread hashes.`);
        } catch (e) {
            consoleError("Error parsing blocked threads from localStorage:", e);
            blockedThreads = new Set();
        }

        // Inject CSS for anchored messages
        const styleElement = document.createElement('style');
        styleElement.textContent = `
            :root {
                --otk-clock-cog-color: #FFD700;
                --otk-clock-bg-color: #181818;
                --otk-clock-text-color: #e6e6e6;
                --otk-clock-border-color: #181818;
                --otk-clock-search-bg-color: #333;
                --otk-clock-search-text-color: #e6e6e6;
                --otk-countdown-bg-color: #181818;
                --otk-gui-bg-color: #181818;
                --otk-gui-text-color: #e6e6e6; /* General text in the main GUI bar */
                --otk-options-text-color: #e6e6e6; /* For text within the options panel */
                --otk-title-text-color: #ff8040; /* Default for main title */
                --otk-stats-text-color: #e6e6e6; /* For the actual stats text numbers in GUI bar */
                --otk-stats-dash-color: #FFD700; /* For the dashes in the stats display */
                --otk-background-updates-stats-text-color: #FFD700; /* For the 'new' stats text */
                --otk-viewer-bg-color: #ffd1a4;
                --otk-gui-threadlist-title-color: #e0e0e0;
                --otk-gui-threadlist-time-color: #FFD700;
                /* Message Styles (Odd Depths: 0, 2, 4...) */
                --otk-msg-depth-odd-content-font-size: 16px;
                --otk-msg-depth-odd-bg-color: #ffffff;
                --otk-msg-depth-odd-text-color: #333333;
                --otk-msg-depth-odd-header-text-color: #555555;
                --otk-viewer-header-border-color-odd: #000000;

                /* Message Styles (Even Depths: 1, 3, 5...) */
                --otk-msg-depth-even-content-font-size: 16px;
                --otk-msg-depth-even-bg-color: #d9d9d9;
                --otk-msg-depth-even-text-color: #333333;
                --otk-msg-depth-even-header-text-color: #555555;
                --otk-viewer-header-border-color-even: #777777;

                --otk-viewer-message-font-size: 13px; /* Default font size for message text - remains common */
                --otk-gui-bottom-border-color: #ff8040; /* Default for GUI bottom border - remains common */
                --otk-cog-icon-color: #FFD700; /* Default for settings cog icon */
                --otk-disable-bg-font-color: #ff8040; /* Default for "Disable Background Updates" text */
                --otk-countdown-timer-text-color: #ff8040; /* Default for countdown timer text */
                --otk-new-messages-divider-color: #000000; /* Default for new message separator line */
                --otk-new-messages-font-color: #000000; /* Default for new message separator text */
                --otk-new-messages-font-size: 16px;

                /* New Depth-Specific Content Font Sizes */
                --otk-msg-depth0-content-font-size: 16px;
                --otk-msg-depth1-content-font-size: 16px;
                --otk-msg-depth2plus-content-font-size: 16px;

                /* GUI Button Colors */
                --otk-button-bg-color: #555;
                --otk-button-text-color: white;
                --otk-button-border-color: #777;
                --otk-button-hover-bg-color: #666;
                --otk-button-active-bg-color: #444444; /* Ensured hex */

                /* Loading Screen Colors */
                --otk-loading-overlay-base-hex-color: #000000; /* Hex base for overlay */
                --otk-loading-overlay-opacity: 1.0;
                --otk-loading-text-color: #ffffff; /* Hex for white */
                --otk-loading-progress-bar-bg-color: #333333; /* Hex for dark grey */
                --otk-loading-progress-bar-fill-color: #4CAF50; /* Already hex */
                --otk-loading-progress-bar-text-color: #ffffff; /* Hex for white */
                /* Add more variables here as they are identified */

                /* Anchor Highlight Colors */
                --otk-anchor-highlight-bg-color: #ff8040;    /* Default: dark yellow/greenish */
                --otk-anchor-highlight-border-color: #000000; /* Default: gold */

                /* Icon Colors */
                --otk-plus-icon-bg-color: #d9d9d9;
                --otk-resize-icon-color: #000000;
                --otk-resize-icon-bg-color: #d9d9d9;
                --otk-blur-icon-color: #000000;
                --otk-blur-icon-bg-color: #d9d9d9;
                --otk-blocked-content-font-color: #e6e6e6;
            }

            /* Refined Chrome Scrollbar Styling for Overlay Effect */
            #otk-messages-container::-webkit-scrollbar {
                width: 8px; /* Thinner for a more subtle overlay appearance */
            }

            #otk-messages-container::-webkit-scrollbar-track {
                background: transparent; /* Make track transparent for overlay effect */
            }

            #otk-messages-container::-webkit-scrollbar-thumb {
                background-color: var(--otk-stats-text-color, #888); /* Use a theme variable, fallback to #888 */
                border-radius: 4px; /* Slightly smaller radius for a thinner bar */
                /* The border creates a visual separation from content, enhancing overlay feel */
                border: 2px solid transparent; /* Keep border transparent initially */
                background-clip: padding-box; /* Ensures background doesn't go under the border */
            }

            #otk-messages-container::-webkit-scrollbar-thumb:hover {
                background-color: #aaa; /* Lighter on hover for better visibility */
                border-color: var(--otk-viewer-bg-color, #181818); /* Show border matching background on hover */
            }
            /* Make scrollbar visible only when scrolling or hovering over the container */
            /* This is harder to achieve with pure CSS for ::-webkit-scrollbar if not natively supported by OS/Browser settings */
            /* The transparent track and subtle thumb provide a good approximation. */
            /* True auto-hide on non-interaction often requires JavaScript or browser/OS support for overlay scrollbars. */

            /* Placeholder styling */
            #otk-custom-theme-name-input::placeholder {
                text-align: center;
            }

            /* GUI Button States */
            .otk-button--hover {
                background-color: var(--otk-button-hover-bg-color) !important;
            }
            .otk-button--active {
                background-color: var(--otk-button-active-bg-color) !important;
            }

            .image-wrapper:not(:hover) .blur-icon {
                display: none;
            }

            #otk-clock-search-icon {
                display: none;
            }
            #otk-clock:hover #otk-clock-search-icon {
                display: inline-block;
            }
            .${ANCHORED_MESSAGE_CLASS} {
                background-color: var(--otk-anchor-highlight-bg-color) !important;
                border: 1px solid var(--otk-anchor-highlight-border-color) !important;
                /* Add other styles if needed, e.g., box-shadow */
            }
                .otk-youtube-embed-wrapper.otk-embed-inline {
                    /* max-width and margins are now controlled by inline styles in createYouTubeEmbedElement */
                    /* This class can be used for other common styles for these embeds if needed */
                }

            /* --- Picture-in-Picture (PiP) Mode --- */
            #otk-resize-handle {
                position: fixed;
                top: 86px; /* Align with bottom of GUI */
                left: 50vw; /* Initial position, will be updated by JS */
                width: 5px;
                height: calc(100% - 86px);
                background-color: #888;
                cursor: col-resize;
                z-index: 10000; /* Above viewer, below options windows */
            }

            /* Class added to body during resize drag to prevent text selection */
            .otk-resizing {
                user-select: none;
                -webkit-user-select: none; /* For Safari */
            }
        `;
        document.head.appendChild(styleElement);
        consoleLog("Injected CSS for anchored messages.");

        await applyMainTheme();
        setupOptionsWindow(); // Call to create the options window shell and event listeners
        setupClockOptionsWindow(); // Create the new clock options window
        setupFilterWindow();
        applyThemeSettings(); // Apply any saved theme settings
        await fetchTimezones();
        setupTimezoneSearch();

        consoleLog('Attempting to call setupLoadingScreen...');
        setupLoadingScreen(); // Create loading screen elements early
        consoleLog('Call to setupLoadingScreen finished.');
        ensureViewerExists(); // Ensure viewer div is in DOM early

        // Note: mediaIntersectionObserver itself is initialized within renderMessagesInViewer

        try {
            consoleLog("Main function start.");
            await initDB();
                consoleLog("IndexedDB initialization attempt complete.");
                messagesByThreadId = await loadMessagesFromDB();
                consoleLog("messagesByThreadId after load:", messagesByThreadId);



                // Recalculate and display initial media stats
                await recalculateAndStoreMediaStats(); // This updates localStorage
                updateDisplayedStatistics(); // This reads from localStorage and updates GUI
                consoleLog("Stats updated.");

                // Restore viewer state
                if (localStorage.getItem(VIEWER_OPEN_KEY) === 'true' && otkViewer) {
                    otkViewer.classList.add('otk-message-layout-default');
                    otkViewer.classList.remove('otk-message-layout-newdesign');
                    consoleLog('Viewer state restored to open. Layout class applied. Rendering all messages.');
                    otkViewer.style.display = 'block';
                    document.body.style.overflow = 'hidden';
                    renderMessagesInViewer({isToggleOpen: true}); // Auto-populate with all messages
                }


                // Load initial data and render list (stats are already updated)
                renderThreadList();
                updateDisplayedStatistics(); // Already called after recalculate

                // Background refresh is no longer started automatically on page load.
                // It is started by clicking "Refresh Data" or by unchecking "Disable Background Updates".
                if (localStorage.getItem(BACKGROUND_UPDATES_DISABLED_KEY) !== 'true') {
                    consoleLog("Background updates are enabled, initiating first check.");
                    startBackgroundRefresh();
                } else {
                    consoleLog("Background updates are disabled by user preference.");
                    const countdownTimer = document.getElementById('otk-countdown-timer');
                    if (countdownTimer) {
                        countdownTimer.textContent = 'n/a';
                    }
                }

                consoleLog("OTK Thread Tracker script initialized and running.");

                setupTitleObserver();

            } catch (error) {
                consoleError("Critical error during main initialization sequence:", error);
                const errorDisplay = document.getElementById('otk-thread-title-display');
                if (errorDisplay) {
                    errorDisplay.textContent = "Tracker Error! Check Console.";
                    errorDisplay.style.color = "red";
                }
            }
        }

        startAutoEmbedReloader();
        startSuspensionChecker();

        // Kick off the script using the main async function
        main().finally(() => {
            // Final verification log after main execution sequence
            const centerInfo = document.getElementById('otk-center-info-container');
            if (centerInfo) {
                consoleLog('[Final Check] Computed flex-grow for centerInfoContainer:', window.getComputedStyle(centerInfo).flexGrow);
            } else {
                consoleWarn('[Final Check] centerInfoContainer not found for flex-grow check.');
            }
        });

        if (localStorage.getItem('otkClockEnabled') === 'true') {
            const clockElement = document.getElementById('otk-clock');
            if (clockElement) {
                clockElement.style.display = 'flex';
                renderClocks();
            }
        }

        setInterval(updateClockTimes, 1000);

        function handleActivity() {
            lastActivityTimestamp = Date.now();
            if (isSuspended) {
                consoleLog("[Activity] Activity detected, resuming background updates.");
                isSuspended = false;
                hideSuspendedScreen();
                startBackgroundRefresh(); // Restart the refresh cycle
            }
        }

        function checkSuspension() {
            if (isSuspended || isManualRefreshInProgress) {
                return;
            }

            const suspendAfterInactiveMinutesValue = localStorage.getItem('otkSuspendAfterInactiveMinutes') || '1';
            if (suspendAfterInactiveMinutesValue === 'Disabled') {
                return;
            }

            const suspendAfterInactiveMinutes = parseInt(suspendAfterInactiveMinutesValue, 10);
            const inactiveMinutes = (Date.now() - lastActivityTimestamp) / (1000 * 60);

            if (inactiveMinutes >= suspendAfterInactiveMinutes) {
                consoleLog(`[Activity] No activity for ${suspendAfterInactiveMinutes} minutes, suspending background updates.`);
                isSuspended = true;
                stopBackgroundRefresh();
                showSuspendedScreen();
            }
        }

        function startSuspensionChecker() {
            if (suspensionCheckIntervalId) {
                clearInterval(suspensionCheckIntervalId);
            }
            suspensionCheckIntervalId = setInterval(checkSuspension, 5000); // Check every 5 seconds

            window.addEventListener('scroll', handleActivity, { passive: true });
            window.addEventListener('mousemove', handleActivity, { passive: true });
            window.addEventListener('mousedown', handleActivity, { passive: true });
            window.addEventListener('keydown', handleActivity, { passive: true });
            window.addEventListener('touchstart', handleActivity, { passive: true });
            document.addEventListener('visibilitychange', handleActivity);
        }

        async function generateMemoryUsageReport() {
            showLoadingScreen("Generating memory usage report...");

            let report = "--- Memory Usage Report ---\n\n";

            // 1. `messagesByThreadId`
            try {
                const messagesSize = new TextEncoder().encode(JSON.stringify(messagesByThreadId)).length;
                report += `messagesByThreadId Size: ${(messagesSize / 1024 / 1024).toFixed(2)} MB\n`;
            } catch (e) {
                report += `messagesByThreadId Size: Error calculating size\n`;
            }

            // 2. IndexedDB
            if (otkMediaDB) {
                try {
                    const transaction = otkMediaDB.transaction(['mediaStore'], 'readonly');
                    const store = transaction.objectStore('mediaStore');
                    const request = store.openCursor();
                    let dbSize = 0;
                    await new Promise((resolve, reject) => {
                        request.onsuccess = (event) => {
                            const cursor = event.target.result;
                            if (cursor) {
                                dbSize += cursor.value.blob.size;
                                cursor.continue();
                            } else {
                                resolve();
                            }
                        };
                        request.onerror = (event) => {
                            reject(event.target.error);
                        };
                    });
                    report += `IndexedDB (mediaStore) Size: ${(dbSize / 1024 / 1024).toFixed(2)} MB\n`;
                    consoleLog(`[Memory Report] IndexedDB (mediaStore) Size: ${(dbSize / 1024 / 1024).toFixed(2)} MB`);
                } catch (e) {
                    report += `IndexedDB (mediaStore) Size: Error calculating size\n`;
                }
            } else {
                report += `IndexedDB (mediaStore) Size: Not available\n`;
            }

            // 3. `tweetCache`
            try {
                const tweetCacheSize = new TextEncoder().encode(JSON.stringify(tweetCache)).length;
                report += `tweetCache Size: ${(tweetCacheSize / 1024).toFixed(2)} KB\n`;
            } catch (e) {
                report += `tweetCache Size: Error calculating size\n`;
            }

            // 4. `createdBlobUrls`
            report += `Created Blob URLs: ${createdBlobUrls.size}\n`;

            // 5. Other data structures
            report += `\n--- Other Data Structures ---\n`;
            report += `activeThreads: ${activeThreads.length} items\n`;

            const themeSettings = JSON.parse(localStorage.getItem(THEME_SETTINGS_KEY)) || {};
            const messageLimitEnabled = themeSettings.otkMessageLimitEnabled !== false;
            const messageLimitValue = parseInt(themeSettings.otkMessageLimitValue || '500', 10);
            report += `Message Limit Enabled: ${messageLimitEnabled}\n`;
            if (messageLimitEnabled) {
                report += `Message Limit Value: ${messageLimitValue}\n`;
            }

            report += `renderedMessageIdsInViewer: ${renderedMessageIdsInViewer.size} items\n`;
            report += `uniqueImageViewerHashes: ${uniqueImageViewerHashes.size} items\n`;
            report += `viewerTopLevelAttachedVideoHashes: ${viewerTopLevelAttachedVideoHashes.size} items\n`;
            report += `viewerTopLevelEmbedIds: ${viewerTopLevelEmbedIds.size} items\n`;

            hideLoadingScreen();

            const reportWindow = window.open("", "Memory Report", "width=600,height=400");
            reportWindow.document.write('<pre>' + report.replace(/\n/g, '<br>') + '</pre>');
        }

    async function fetchTimezones() {
        return new Promise((resolve) => {
            GM_xmlhttpRequest({
                method: "GET",
                url: 'https://github.com/johnt1884/ff/releases/download/firefox/cities_geonames.json',
                onload: function(response) {
                    if (response.status === 200) {
                        try {
                            cityData = JSON.parse(response.responseText);
                            consoleLog(`Successfully fetched and parsed ${cityData.length} cities.`);
                        } catch (e) {
                            consoleError("Failed to parse city data JSON:", e);
                            cityData = []; // Ensure it's an empty array on error
                        }
                    } else {
                        consoleError(`Failed to fetch city data: ${response.status}`);
                        cityData = [];
                    }
                    resolve();
                },
                onerror: function(error) {
                    consoleError('Error fetching city data:', error);
                    cityData = [];
                    resolve();
                }
            });
        });
    }

    function setupTimezoneSearch() {
        const searchInput = document.getElementById('otk-timezone-search-input');
        const searchResultsDiv = document.getElementById('otk-timezone-search-results');

        function addZoneItem(city) {
            const resultDiv = document.createElement('div');
            // Display format: "City, State (Country)"
            const displayText = `${city.city}, ${city.admin1} (${city.country_code})`;
            resultDiv.textContent = displayText;
            resultDiv.dataset.timezone = city.timezone;
            resultDiv.style.cssText = `
                padding: 4px;
                cursor: pointer;
                color: var(--otk-clock-search-text-color, #e6e6e6);
            `;
            resultDiv.addEventListener('mouseenter', () => {
                resultDiv.style.backgroundColor = '#555';
            });
            resultDiv.addEventListener('mouseleave', () => {
                resultDiv.style.backgroundColor = '';
            });
            resultDiv.addEventListener('click', () => {
                const selectedTimezone = resultDiv.dataset.timezone;
                let clocks = JSON.parse(localStorage.getItem('otkClocks') || '[]');
                const clockIndex = clocks.findIndex(c => c.id === activeClockSearchId);

                if (clockIndex !== -1) {
                    clocks[clockIndex].timezone = selectedTimezone;
                    clocks[clockIndex].displayPlace = city.city;
                    localStorage.setItem('otkClocks', JSON.stringify(clocks));
                }

                renderClocks(); // Re-render to show changes
                renderClockOptions(); // Re-render the options list
                document.getElementById('otk-timezone-search-container').style.display = 'none'; // Hide search
                searchInput.value = '';
                searchResultsDiv.innerHTML = '';
                activeClockSearchId = null; // Reset active clock
            });
            searchResultsDiv.appendChild(resultDiv);
        }

        searchInput.addEventListener('input', () => {
            const query = searchInput.value.trim().toLowerCase();
            searchResultsDiv.innerHTML = '';

            if (query.length < 2) {
                return;
            }

            const queryWords = query.split(/\s+/).filter(w => w.length > 0);

            const results = cityData.filter(city => {
                const fullCityName = `${city.city}, ${city.admin1}`.toLowerCase();
                // Check if all query words are present in the city name
                return queryWords.every(word => fullCityName.includes(word));
            });

            // Sort results by population (descending)
            results.sort((a, b) => b.population - a.population);

            // Display top results
            results.slice(0, 50).forEach(city => {
                addZoneItem(city);
            });
        });
    }

})();
