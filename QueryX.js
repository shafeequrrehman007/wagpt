// Import required modules
const {
  BufferJSON,
  WA_DEFAULT_EPHEMERAL,
  generateWAMessageFromContent,
  proto,
  generateWAMessageContent,
  generateWAMessage,
  prepareWAMessageMedia,
  areJidsSameUser,
  getContentType,
} = require("@whiskeysockets/baileys"); // Use the official package name
const fsPromises = require("fs").promises; // Use fs.promises for async file operations
const fs = require("fs"); // Use regular fs for sync operations
const path = require("path"); // Import path module
const util = require("util");
const chalk = require("chalk");
const { GoogleGenerativeAI, HarmCategory, HarmBlockThreshold } = require("@google/generative-ai");
const axios = require("axios");
const sharp = require("sharp"); // Add sharp for image processing
const { Readable } = require('stream');
const { promisify } = require('util');
const stream = require('stream');
const pipeline = promisify(stream.pipeline);

// --- Configuration and State ---

// Configuration file paths
const CONFIG_PATH = path.join(__dirname, "key.json");
const PROMPT_PATH = path.join(__dirname, "custom_prompt.txt");
const HISTORY_PATH = path.join(__dirname, "chat_history.json");

let config = {}; // Store loaded configuration
let customPrompt = ""; // Store loaded custom prompt
let chatHistory = {}; // Store chat history in memory

// Gemini AI state
let genAI;
let geminiModel = null; // Store the initialized model instance

// Rate limit tracking (global simple limit)
let rateLimitCount = 0;
const RATE_LIMIT_THRESHOLD = 1000; // Max requests per window
const RATE_LIMIT_WINDOW = 60000; // Window duration in milliseconds (60 seconds)
let rateLimitTimer = null; // Timer to reset the rate limit count

// Add message deduplication tracking
const processedMessages = new Set();
const MESSAGE_EXPIRY = 5 * 60 * 1000; // 5 minutes in milliseconds

// Enhance rate limiting
const userRateLimits = new Map();
const USER_RATE_LIMIT = 100; // messages per minute per user
const USER_RATE_WINDOW = 60000; // 1 minute in milliseconds

// Add chat history command constants
const CHAT_COMMANDS = {
    CLEAR: '!clear',
    HISTORY: '!history',
    CONTEXT: '!context',
    FORGET: '!forget',
    REMEMBER: '!remember'
};

const HISTORY_LIMITS = {
    MAX_MESSAGES: 50,          // Maximum messages to store per user
    MAX_DISPLAY: 10,          // Maximum messages to show in history command
    MAX_CONTEXT_LENGTH: 2000  // Maximum characters for context
};

// Update the HELP_TEXT constant to use proper WhatsApp markdown
const HELP_TEXT = `
🤖 _WhatsApp Bot Commands_

*Chat History Commands*
• !history - Show your recent chat history
• !context - Show current context status
• !forget - Clear your chat history
• !remember [text] - Add text to chat context
• !clear - Clear current conversation

*Image Commands*
• !img [query] - Search for images
• !searchimg - Search using uploaded image (send command with image)
• !describe - Get description of uploaded image (send command with image)

*Other Commands*
• !ping - Check bot response time
• !test - Test if bot is working

_Send any message to chat with the bot!_
`;

// --- Utility Functions ---

/**
 * Reads data from a JSON file.
 * @param {string} filePath - The path to the JSON file.
 * @returns {Promise<object>} - The parsed JSON object.
 */
async function readJsonFile(filePath) {
  try {
    // Check if file exists
    try {
      await fsPromises.access(filePath);
    } catch (error) {
      // File doesn't exist, create it with default structure
      const defaultContent = {
        version: "1.0",
        histories: {}
      };
      await writeJsonFile(filePath, defaultContent);
      return defaultContent;
    }

    // Read and parse file
    const data = await fsPromises.readFile(filePath, "utf-8");
    
    // Handle empty file
    if (!data || data.trim() === "") {
      const defaultContent = {
        version: "1.0",
        histories: {}
      };
      await writeJsonFile(filePath, defaultContent);
      return defaultContent;
    }

    try {
      return JSON.parse(data);
    } catch (parseError) {
      console.error(chalk.red(`Error parsing JSON in ${filePath}. Creating new file.`));
      const defaultContent = {
        version: "1.0",
        histories: {}
      };
      await writeJsonFile(filePath, defaultContent);
      return defaultContent;
    }
  } catch (error) {
    console.error(chalk.red(`Error reading file ${filePath}:`), error);
    // Return empty default structure instead of throwing
    return {
      version: "1.0",
      histories: {}
    };
  }
}

/**
 * Reads data from a text file.
 * @param {string} filePath - The path to the text file.
 * @returns {Promise<string>} - The file content.
 */
async function readTextFile(filePath) {
  try {
    return await fsPromises.readFile(filePath, "utf-8");
  } catch (error) {
    if (error.code === "ENOENT") {
      console.warn(chalk.yellow(`File not found: ${filePath}. Returning empty string.`));
      return ""; // Return empty string if file doesn't exist
    }
    console.error(chalk.red(`Error reading file ${filePath}:`), error);
    throw error; // Re-throw other errors
  }
}

/**
 * Writes data to a JSON file.
 * @param {string} filePath - The path to the JSON file.
 * @param {object} data - The data to write.
 */
async function writeJsonFile(filePath, data) {
  try {
    const jsonString = JSON.stringify(data, null, 2);
    await fsPromises.writeFile(filePath, jsonString, "utf-8");
  } catch (error) {
    console.error(chalk.red(`Error writing file ${filePath}:`), error);
    // Consider more robust error handling or logging here
  }
}

/**
 * Format chat history for display
 * @param {Array} history - Array of chat messages
 * @param {number} limit - Maximum number of messages to display
 * @returns {string} Formatted chat history
 */
function formatChatHistory(history, limit = HISTORY_LIMITS.MAX_DISPLAY) {
    if (!history || history.length === 0) return "No chat history available.";
    
    const recentHistory = history.slice(-limit);
    return recentHistory.map((msg, index) => {
        const role = msg.role === 'user' ? '👤 You' : '🤖 Bot';
        const content = msg.parts[0].text;
        return `${index + 1}. ${role}:\n${content}\n`;
    }).join('\n');
}

/**
 * Updates chat history for a specific sender.
 * @param {string} sender - The sender's JID.
 * @param {object} message - The message object to add.
 */
async function updateChatHistory(sender, message) {
    try {
        // Read current history
        const historyData = await readJsonFile(HISTORY_PATH);
        
        // Ensure histories object exists
        if (!historyData.histories) {
            historyData.histories = {};
        }
        
        // Initialize sender's history if needed
        if (!historyData.histories[sender]) {
            historyData.histories[sender] = [];
        }

        // Add message with timestamp
        const messageWithTimestamp = {
            role: message.role === "user" ? "user" : "model",
            parts: [{ text: message.content }],
            timestamp: Date.now()
        };

        historyData.histories[sender].push(messageWithTimestamp);

        // Keep history length limited
        if (historyData.histories[sender].length > HISTORY_LIMITS.MAX_MESSAGES) {
            historyData.histories[sender] = historyData.histories[sender].slice(-HISTORY_LIMITS.MAX_MESSAGES);
        }

        // Save updated history
        await writeJsonFile(HISTORY_PATH, historyData);
    } catch (error) {
        console.error(chalk.red("Error updating chat history:"), error);
        // Don't throw, just log the error
    }
}

/**
 * Resets the global rate limit count after a window.
 */
function resetRateLimit() {
    console.log(chalk.yellow(`Rate limit window ended. Resetting count from ${rateLimitCount} to 0.`));
    rateLimitCount = 0;
    rateLimitTimer = null; // Clear the timer ID
}

/**
 * Starts the rate limit timer if not already running.
 */
function startRateLimitTimer() {
    if (!rateLimitTimer) {
        rateLimitTimer = setTimeout(resetRateLimit, RATE_LIMIT_WINDOW);
    }
}

/**
 * Checks if the rate limit has been exceeded.
 * @returns {boolean} - True if rate limited, false otherwise.
 */
function isRateLimited() {
    return rateLimitCount >= RATE_LIMIT_THRESHOLD;
}

/**
 * Increments the rate limit counter and starts the timer.
 */
function incrementRateLimit() {
    rateLimitCount++;
    startRateLimitTimer();
}

/**
 * Checks if a message has been processed recently
 * @param {string} messageId - The ID of the message
 * @returns {boolean} - True if message was already processed
 */
function isMessageProcessed(messageId) {
    return processedMessages.has(messageId);
}

/**
 * Marks a message as processed
 * @param {string} messageId - The ID of the message
 */
function markMessageProcessed(messageId) {
    processedMessages.add(messageId);
    // Remove the message ID after expiry time
    setTimeout(() => {
        processedMessages.delete(messageId);
    }, MESSAGE_EXPIRY);
}

/**
 * Checks if a user is rate limited
 * @param {string} userId - The user's ID
 * @returns {boolean} - True if user is rate limited
 */
function isUserRateLimited(userId) {
    if (!userRateLimits.has(userId)) {
        userRateLimits.set(userId, {
            count: 0,
            timer: null
        });
    }

    const userLimit = userRateLimits.get(userId);
    
    if (userLimit.count >= USER_RATE_LIMIT) {
        return true;
    }

    userLimit.count++;
    if (!userLimit.timer) {
        userLimit.timer = setTimeout(() => {
            userRateLimits.delete(userId);
        }, USER_RATE_WINDOW);
    }

    return false;
}

// --- Initialization Functions ---

/**
 * Validates the provided Gemini API key.
 * Throws an error if the key is invalid or not set.
 */
async function validateApiKey() {
  const apiKey = config.keygemini;
  if (!apiKey || apiKey === "ENTER YOUR GEMINI API KEY HERE") {
    throw new Error("Gemini API key not configured. Please set your key in key.json");
  }

  if (!apiKey.startsWith("AIza")) {
     console.warn(chalk.yellow("Warning: Gemini API keys usually start with 'AIza'. Double check your key format."));
  }

  try {
      genAI = new GoogleGenerativeAI(apiKey);
      const model = genAI.getGenerativeModel({ model: "gemini-2.0-flash" });
      const result = await model.generateContent("test");
      if (result && result.response) {
          console.log(chalk.green("Gemini API key validation successful."));
          return true;
      }
  } catch (error) {
      console.error(chalk.red("Gemini API key validation failed:"), error.message);
      console.error(chalk.red("Ensure your API key is correct and has access to the Gemini API."));
      throw new Error("Gemini API key validation failed.");
  }
}

/**
 * Initializes the Gemini model by trying available models.
 * Stores the successful model instance in `geminiModel`.
 */
async function initializeGeminiModel() {
  if (!genAI) {
      throw new Error("GoogleGenerativeAI instance not initialized. Call validateApiKey first.");
  }

  try {
      const model = genAI.getGenerativeModel({ 
        model: "gemini-2.0-flash",
        generationConfig: {
          maxOutputTokens: 50000,
          temperature: 1.0,
        
        }
      });

      const result = await model.generateContent("test model availability");
      if (result && result.response) {
          console.log(chalk.green("Successfully initialized Gemini model"));
          geminiModel = model;
          return;
      }
  } catch (error) {
      console.error(chalk.red("Failed to initialize Gemini model:"), error.message);
      throw error;
  }
}

/**
 * Loads configuration, history, prompt, validates API key, and initializes the Gemini model.
 */
async function initBot() {
    try {
        console.log(chalk.blue("Initializing bot..."));

        // Load configuration
        config = await readJsonFile(CONFIG_PATH);
        if (!config || Object.keys(config).length === 0) {
             console.error(chalk.red(`Configuration file not found or is empty: ${CONFIG_PATH}. Please create key.json with your API keys.`));
             // Keep bot inactive or throw error depending on desired behavior
             throw new Error("Bot configuration missing.");
        }
        console.log(chalk.green("Configuration loaded successfully."));

        // Load custom prompt
        customPrompt = await readTextFile(PROMPT_PATH);
        if (customPrompt) {
             console.log(chalk.green("Custom prompt loaded successfully."));
        } else {
             console.warn(chalk.yellow(`Custom prompt file not found or is empty: ${PROMPT_PATH}. Bot will use default behavior.`));
        }

        // Load chat history
        chatHistory = await readJsonFile(HISTORY_PATH);
        console.log(chalk.green("Chat history loaded successfully."));

        // Validate API key and initialize Gemini AI instance
        await validateApiKey();

        // Initialize Gemini Model
        await initializeGeminiModel();

        console.log(chalk.green("Bot initialization complete. Ready to receive messages."));

    } catch (error) {
        console.error(chalk.red("Bot failed to initialize:"), error);
        // The bot will not be fully functional as geminiModel will be null
        geminiModel = null; // Ensure model is null on failure
        genAI = null; // Ensure genAI is null on failure
    }
}


// --- Feature Functions ---

/**
 * Function to search images using Google Custom Search API.
 * @param {string} query - The search query.
 * @param {number} [num=5] - Number of images to search.
 * @returns {Promise<Array<{url: string, title: string, thumbnail: string}>>} - Array of image results.
 */
async function searchImages(query, num = 5) {
  const searchEngineId = config.searchEngineId;
  const apiKey = config.googleApiKey;
  
  if (!searchEngineId || !apiKey) {
    throw new Error("Google Search Engine ID or API Key not configured in key.json");
  }

  const searchUrl = `https://www.googleapis.com/customsearch/v1beta`;
  const response = await axios.get(searchUrl, {
    params: {
      key: apiKey,
      cx: searchEngineId,
      q: query,
      searchType: 'image',
      num: num,
      safe: 'active'
    },
    timeout: 15000
  });

  return response.data.items
    .filter(item => item.link && item.title)
    .map(item => ({
      url: item.link,
      title: item.title,
      thumbnail: item.image?.thumbnailLink
    }));
}

/**
 * Function to send an image message from a URL.
 * @param {*} m - The message object from Baileys.
 * @param {string} imageUrl - The URL of the image.
 * @param {string} [caption=""] - The caption for the image.
 */
async function sendImageMessage(m, imageUrl, caption = "") {
  try {
      console.log(chalk.blue(`Sending image: ${imageUrl}`));
      const response = await axios.get(imageUrl, { responseType: 'arraybuffer', timeout: 10000 }); // Add timeout
      const buffer = Buffer.from(response.data, 'binary');

      const message = {
        image: buffer,
        caption: caption,
        contextInfo: m.quoted ? {
             participant: m.quoted.sender,
             stanzaId: m.quoted.id,
             isForwarded: false,
             quotedMessage: m.quoted.message
        } : {} // Optional: quote the original message
      };

      await m.reply(message);
      console.log(chalk.green("Image sent successfully."));
  } catch (error) {
      console.error(chalk.red(`Error sending image from URL ${imageUrl}:`), error);
      m.reply(`❌ Failed to send image: ${error.message}`); // Inform user about failure
  }
}

/**
 * Process and optimize image buffer
 * @param {Buffer} imageBuffer - Raw image buffer
 * @returns {Promise<Buffer>} - Processed image buffer
 */
async function processImage(imageBuffer) {
    try {
        const processed = await sharp(imageBuffer)
            .resize(800, 800, { // Resize to reasonable dimensions
                fit: 'inside',
                withoutEnlargement: true
            })
            .jpeg({ quality: 80 }) // Convert to JPEG with good quality
            .toBuffer();
        return processed;
    } catch (error) {
        console.error(chalk.red("Error processing image:"), error);
        throw error;
    }
}

/**
 * Extract image from message
 * @param {*} m - Message object
 * @returns {Promise<Buffer>} - Image buffer
 */
async function getImageFromMessage(m) {
    try {
        if (m.quoted && m.quoted.mtype === 'imageMessage') {
            return await m.quoted.download();
        } else if (m.mtype === 'imageMessage') {
            return await m.download();
        }
        return null;
    } catch (error) {
        console.error(chalk.red("Error downloading image:"), error);
        throw error;
    }
}

/**
 * Get image description using Gemini Vision
 * @param {Buffer} imageBuffer - The image buffer
 * @param {string} prompt - Optional prompt for the model
 * @returns {Promise<string>} - Image description
 */
async function getImageDescription(imageBuffer, prompt = "Describe this image in detail") {
    try {
        if (!genAI) throw new Error("Gemini AI not initialized");

        const model = genAI.getGenerativeModel({ model: "gemini-pro-vision" });
        
        // Convert buffer to base64
        const base64Image = imageBuffer.toString('base64');
        
        const result = await model.generateContent([
            prompt,
            {
                inlineData: {
                    data: base64Image,
                    mimeType: "image/jpeg"
                }
            }
        ]);

        const response = await result.response;
        return response.text();
    } catch (error) {
        console.error(chalk.red("Error getting image description:"), error);
        throw error;
    }
}

/**
 * Format WhatsApp message text
 * @param {string} text - The text to format
 * @returns {string} - Formatted text
 */
function formatWhatsAppMessage(text) {
    if (!text) return text;

    // Convert **bold** to *bold* for WhatsApp
    text = text.replace(/\*\*(.*?)\*\*/g, '*$1*');
    
    // Handle any remaining double asterisks
    text = text.replace(/\*\*/g, '*');
    
    // Remove empty bold tags
    text = text.replace(/\*\s*\*/g, '');
    
    // Ensure proper spacing around bold text
    text = text.replace(/(\w)\*(\w)/g, '$1 *$2');
    text = text.replace(/(\w)\*([^*\s])/g, '$1 *$2');
    text = text.replace(/([^*\s])\*(\w)/g, '$1* $2');
    
    // Convert markdown lists to WhatsApp bullet points
    text = text.replace(/^\* /gm, '• ');
    
    // Ensure proper spacing after bullet points
    text = text.replace(/•(\w)/g, '• $1');

    return text;
}

// Update the message reply function to use formatting
async function sendFormattedReply(m, text) {
    const formattedText = formatWhatsAppMessage(text);
    await m.reply(formattedText);
}

// --- Main Message Handler ---

/**
 * The main function that handles incoming messages.
 * @param {*} client - The Baileys client instance.
 * @param {*} m - The message object.
 * @param {*} chatUpdate - The chat update object.
 * @param {*} store - The Baileys store object.
 */
module.exports = sansekai = async (client, m, chatUpdate, store) => {
  try {
      // Early return conditions to prevent loops
      if (!m) return;
      if (!m.message) return;
      if (m.key && m.key.remoteJid === "status@broadcast") return;
      if (!client.public && !m.key.fromMe && chatUpdate.type === "notify") return;
      if (m.key.id.startsWith("BAE5") && m.key.id.length === 16) return;

      // Check for message deduplication
      if (isMessageProcessed(m.key.id)) {
          console.log(chalk.yellow(`Duplicate message detected: ${m.key.id}`));
          return;
      }

      // Check user rate limit
      const senderId = m.sender || m.key.remoteJid;
      if (isUserRateLimited(senderId)) {
          console.log(chalk.yellow(`Rate limit exceeded for user: ${senderId}`));
          await client.sendMessage(m.chat, { 
              text: "Please wait a moment before sending more messages." 
          });
          return;
      }

      // Mark message as processed
      markMessageProcessed(m.key.id);

      // Ignore if bot is not initialized
      if (!geminiModel || !config || !genAI) {
          console.log(chalk.yellow("Bot not fully initialized. Ignoring message."));
          return;
      }

      const text = m.text;
      // Ignore if message is empty or just whitespace
      if (!text || text.trim().length === 0) {
          return;
      }

      const isCmd = text && text.startsWith(config.prefix || "!");
      const command = isCmd ? text.slice(config.prefix.length).trim().split(/ +/).shift().toLowerCase() : null;
      const args = isCmd ? text.slice(config.prefix.length).trim().split(/ +/).slice(1).join(" ") : null;

      // Ignore if message is not text or doesn't have content
      if (!m.message || !text) {
          return;
      }

      // Check if message is from owner (using configurable owner JID)
      const ownerJid = config.ownerJid;
      const isOwner = ownerJid && m.sender === ownerJid;

      // --- Handle Specific Commands ---
      if (isCmd) {
          console.log(chalk.cyan(`Command received: ${command} from ${m.sender}`));
          switch (command) {
              case "start":
                  if (isOwner) {
                      m.reply("🤖 Bot is active and ready!");
                  } else {
                      m.reply("Unauthorized command.");
                  }
                  break;

              case "ping":
                   const start = Date.now();
                   await m.reply("Pong!");
                   const end = Date.now();
                   m.reply(`Latency: ${end - start}ms`);
                   break;

              case "clearchat":
                   if (chatHistory[m.sender]) {
                       delete chatHistory[m.sender];
                       await writeJsonFile(HISTORY_PATH, chatHistory);
                       m.reply("✅ Your chat history has been cleared.");
                       console.log(chalk.green(`Chat history cleared for ${m.sender}`));
                   } else {
                       m.reply("Your chat history is already empty.");
                   }
                   break;

              case "img":
              case "image":
                  if (!args) {
                      m.reply(`Please provide a search query. Example: ${config.prefix}img cute cats`);
                      return;
                  }
                  m.reply("🔍 Searching for images...");
                  try {
                      const images = await searchImages(args, 5); // Search for 5 images
                      if (images.length > 0) {
                           // Send first image with caption
                           await sendImageMessage(m, images[0].url, `📸 ${images[0].title}\n\nSearch query: "${args}"`);

                           // Send remaining images without caption to avoid spamming long text
                           for (let i = 1; i < images.length; i++) {
                             // Add a small delay between sending multiple images to avoid flooding
                             await new Promise(resolve => setTimeout(resolve, 500));
                             await sendImageMessage(m, images[i].url); // Send without caption
                           }
                      } else {
                          m.reply(`❌ No images found for "${args}".`);
                      }
                  } catch (error) {
                      console.error(chalk.red("Image search command failed:"), error);
                      m.reply(`❌ Error during image search: ${error.message}`);
                  }
                  break;

              case "test":
                  // Placeholder for testing commands
                   m.reply("Test command executed.");
                  break;

              // Handle ignored commands if they were explicitly handled before, or remove
              case "ai": // If these were ignored before, maybe they activate/deactivate AI?
              case "gemini": // Let's remove the explicit ignore unless there's a reason
                  // If you want to explicitly activate AI:
                  // m.reply("AI mode activated.");
                  // return; // Stop processing as a command
                  // If you want to explicitly ignore:
                   console.log(chalk.yellow(`Ignoring explicit AI command: ${command}`));
                   return; // Stop processing this message
                  break; // unreachable if return is used

              case "history":
                  const historyData = await readJsonFile(HISTORY_PATH);
                  const userHistory = historyData.histories[m.sender] || [];
                  const formattedHistory = formatChatHistory(userHistory);
                  await sendFormattedReply(m, `📜 Your Chat History:\n\n${formattedHistory}`);
                  break;

              case "context":
                  const currentContext = chatHistory[m.sender] || [];
                  const contextSummary = currentContext.length > 0 
                      ? `Currently using ${currentContext.length} messages of context.`
                      : "No active context.";
                  await sendFormattedReply(m, contextSummary);
                  break;

              case "forget":
                  if (chatHistory[m.sender]) {
                      delete chatHistory[m.sender];
                      await writeJsonFile(HISTORY_PATH, chatHistory);
                      await sendFormattedReply(m, "🗑️ Chat history and context cleared.");
                  } else {
                      await sendFormattedReply(m, "No history to clear.");
                  }
                  break;

              case "remember":
                  if (!args) {
                      await sendFormattedReply(m, "Please provide text to remember in the context.");
                      return;
                  }
                  await updateChatHistory(m.sender, {
                      role: "user",
                      content: args
                  });
                  await sendFormattedReply(m, "✅ Added to chat context.");
                  break;

              case "help":
                  await sendFormattedReply(m, HELP_TEXT);
                  break;

              case "searchimg":
              case "describe":
                  try {
                      const imageBuffer = await getImageFromMessage(m);
                      if (!imageBuffer) {
                          await sendFormattedReply(m, "Please send an image with this command or reply to an image with this command.");
                          return;
                      }

                      await sendFormattedReply(m, "🔍 Processing image...");
                      
                      // Process image to optimize size and format
                      const processedImage = await processImage(imageBuffer);
                      
                      // Get description based on command
                      const prompt = command === "searchimg" 
                          ? "What is shown in this image? Provide a detailed search query that could find similar images."
                          : "Describe this image in detail, including any text, objects, people, or notable features.";
                      
                      const description = await getImageDescription(processedImage, prompt);
                      
                      if (command === "searchimg") {
                          await sendFormattedReply(m, `🔍 Searching for similar images based on: ${description}`);
                          const images = await searchImages(description, 5);
                          
                          if (images.length > 0) {
                              await sendImageMessage(m, images[0].url, `Found similar images based on analysis:\n${description}`);
                              
                              for (let i = 1; i < images.length; i++) {
                                  await new Promise(resolve => setTimeout(resolve, 500));
                                  await sendImageMessage(m, images[i].url);
                              }
                          } else {
                              await sendFormattedReply(m, "❌ No similar images found.");
                          }
                      } else {
                          await sendFormattedReply(m, `📝 *Image Analysis*:\n\n${description}`);
                      }
                  } catch (error) {
                      console.error(chalk.red("Error processing image command:"), error);
                      await sendFormattedReply(m, "❌ Error processing image. Please try again.");
                  }
                  break;

              default:
                  await sendFormattedReply(m, `❓ Unknown command: ${config.prefix}${command}\nType ${config.prefix}help for available commands.`);
                  break;
          }
          return;
      }

      // --- Process Regular Text Messages with AI ---
      // Check for rate limit before calling AI
      if (isRateLimited()) {
           console.log(chalk.yellow(`Rate limited: ${m.sender}`));
           return;
      }

      // Get user's chat history or initialize it
      const userHistory = chatHistory[m.sender] || [];

      // Prepare history for Gemini API, including the custom prompt if available
      let conversationHistory = [];

      // Add custom prompt as an initial user message if available
      if (customPrompt) {
         conversationHistory.push({ role: 'user', parts: [{ text: customPrompt }] });
      }

      // Add previous chat history
      conversationHistory = conversationHistory.concat(userHistory);

      // Add the current user message
      const currentUserMessage = { role: 'user', parts: [{ text: text }] };
      conversationHistory.push(currentUserMessage);

      console.log(chalk.blue(`Processing message from ${m.sender}: "${text.substring(0, 50)}..."`));

      try {
          incrementRateLimit();

          const chatInstance = geminiModel.startChat({
              history: conversationHistory.slice(0, -1),
              generationConfig: geminiModel.generationConfig,
          });

          const result = await chatInstance.sendMessage(text);
          const response = await result.response;
          const responseText = response.text();

          if (!responseText || responseText.trim().length === 0) {
              console.warn(chalk.yellow("Empty response from Gemini. Not sending reply."));
              return;
          }

          // Format the response text before sending
          const formattedResponse = formatWhatsAppMessage(responseText);

          // Update chat history only after a successful response
          await updateChatHistory(m.sender, { role: "user", content: text });
          await updateChatHistory(m.sender, { role: "assistant", content: formattedResponse });

          console.log(chalk.green(`Response generated for ${m.sender}.`));
          await sendFormattedReply(m, formattedResponse);

      } catch (error) {
          console.error(chalk.red(`Error processing message for ${m.sender}:`), error);
          // Don't send error messages to user
          return;
      }
  } catch (mainError) {
      console.error(chalk.red("Unhandled error in message handler:"), mainError);
      // Don't send error messages to user
      return;
  }
};

// --- Startup and Reload Logic ---

// Initialize the bot when the script starts
initBot();

// Watch for changes in this file and reload the code if changes are detected
let file = require.resolve(__filename);
fs.watchFile(file, () => {
  fs.unwatchFile(file);
  console.log(chalk.redBright(`Update ${__filename}`));
  delete require.cache[file];
  require(file);
});

// Note: Changes to key.json, custom_prompt.txt, or chat_history.json will require
// a manual restart or additional watch logic for those files if you want them
// to be reloaded automatically without changing this main script file.