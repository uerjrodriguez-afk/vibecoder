/*
 * Vibecoder Incremental — game engine.
 *
 * Everything the player reads lives in locales/*.js. This file only holds
 * numbers, rules and rendering. Arrays here (PRODUCERS, SETUP, the shelves)
 * are matched to the locale arrays by position.
 *
 * Economy in one paragraph: every click spends tokens. Every token spent is
 * added to the run total (the score) and to the budget (the currency).
 * Producers spend tokens on their own. Library files are bought one by one,
 * in order, and each one multiplies everything by 1.05. Technical debt grows
 * while producers run and cuts their output by up to 70%. Buying all 30
 * files unlocks /clear, the prestige reset, which doubles all output.
 */
"use strict";

const $ = selector => document.querySelector(selector);
const $$ = selector => Array.from(document.querySelectorAll(selector));
const SAVE_KEY = "vibecoder-incremental-v2";
const DEFAULT_LANGUAGE = "en";

/* ================= GAME DATA ================= */

// Base cost and base tokens per second for each producer.
const PRODUCERS = [
  { cost: 15, rate: 0.1 },
  { cost: 100, rate: 1 },
  { cost: 1100, rate: 8 },
  { cost: 12000, rate: 47 },
  { cost: 130000, rate: 260 },
  { cost: 1.4e6, rate: 1400 },
  { cost: 2e7, rate: 7800 },
  { cost: 3.3e8, rate: 44000 },
  { cost: 5.1e9, rate: 260000 },
  { cost: 7.5e10, rate: 1.6e6 }
];
const PRODUCER_GROWTH = 1.15;               // each unit makes the next 15% pricier
const PRODUCER_MILESTONES = [10, 25, 50, 100, 200]; // each one doubles that producer

// Click upgrades. `growth` multiplies the price at each level.
const SETUP = [
  { id: "prompt", cost: 30, growth: 6, max: Infinity }, // doubles tokens per click
  { id: "context", cost: 800, growth: 7, max: 20 },     // +10% producer output per level
  { id: "tab", cost: 4000, growth: 9, max: 10 }          // click adds 1% of per-second rate per level
];

// The library: three shelves of ten files each, sold one at a time and in order.
const SHELVES = [
  { id: "skills", glyph: "/", type: "skill", file: "SKILL.md", price: i => 100 * Math.pow(7, i) },
  { id: "plugins", glyph: "+", type: "plugin", file: "SKILL.md", price: i => 2500 * Math.pow(8, i), opensAt: 2000 },
  { id: "agents", glyph: "@", type: "agent", file: "AGENT.md", price: i => PRODUCERS[i].cost * 60 }
];
const SHELF = Object.fromEntries(SHELVES.map(s => [s.id, s]));
const FILES_PER_SHELF = 10;
const TOTAL_FILES = SHELVES.length * FILES_PER_SHELF;
const LIBRARY_MULTIPLIER = 1.05;  // per file owned
const SKILL_CLICK_MULTIPLIER = 2;
const SKILL_READ_MULTIPLIER = 1.25;
const PLUGIN_OUTPUT_MULTIPLIER = 1.5;
const AGENT_PRODUCER_MULTIPLIER = 3;
const DEBT_BRAKE_PLUGINS = [3, 7, 9]; // focus-mode, four-day-week, dignity
const DEBT_BRAKE_FACTOR = 0.75;

// Technical debt, in percent (0–100).
const DEBT_PER_CLICK = 0.012;
const DEBT_PER_PRODUCER_TYPE_PER_SECOND = 0.0025;
const DEBT_MAX_PENALTY = 0.7;        // at 100% debt, producers yield 30%
const READ_BASE = 0.6;               // percent removed per "read the code" click
const REWRITE_KEEPS = 0.4;           // a rewrite keeps 40% of the debt
const REWRITE_BUDGET_SHARE = 0.25;

// Leaderboard tiers, by tokens spent this run. Names come from the locale.
const TIER_THRESHOLDS = [0, 500, 5e4, 5e6, 5e8, 5e10, 5e12, 5e14];

const MODES = { standard: { output: 1, cost: 1 }, hardcore: { output: 0.75, cost: 1.5 }, speedrun: { output: 1, cost: 1 } };
const OFFLINE_CAP_SECONDS = 8 * 3600;
const OFFLINE_EFFICIENCY = 0.5;
const TICK_MS = 100;
const REPOSITORY_URL = "https://github.com/uerjrodriguez-afk/vibecoder";

/* ================= LOCALES ================= */

let language = DEFAULT_LANGUAGE;
const locale = () => window.LOCALES[language] || window.LOCALES[DEFAULT_LANGUAGE];
const english = () => window.LOCALES[DEFAULT_LANGUAGE];

function lookup(root, path) {
  return path.split(".").reduce((node, key) => (node == null ? undefined : node[key]), root);
}
// Returns the string (or function, or array) at `path`, falling back to English.
function t(path) {
  const value = lookup(locale(), path);
  return value === undefined ? lookup(english(), path) : value;
}
// Calls the locale function at `path` with `args`, or returns the plain value.
function tf(path, ...args) {
  const value = t(path);
  return typeof value === "function" ? value(...args) : value;
}
// One library file's text, with English filling any gap.
function fileText(shelfId, index) {
  const own = (lookup(locale(), "library." + shelfId) || [])[index] || {};
  const fallback = english().library[shelfId][index];
  return Object.assign({}, fallback, own);
}
const listText = (path, index) => (t(path) || [])[index] || lookup(english(), path)[index];

/* ================= STATE ================= */

function newRun(carry) {
  return {
    version: 2,
    runTokens: 0, budget: 0, clicks: 0, linesRead: 0, rewrites: 0,
    producers: PRODUCERS.map(() => 0),
    setup: { prompt: 0, context: 0, tab: 0 },
    owned: { skills: Array(FILES_PER_SHELF).fill(false), plugins: Array(FILES_PER_SHELF).fill(false), agents: Array(FILES_PER_SHELF).fill(false) },
    readThisRun: {}, debt: 0, startedAt: Date.now(), playSeconds: 0, missionShown: false, speedrunTime: null,
    // carried across /clear
    stars: carry ? carry.stars : 0,
    lifetimeTokens: carry ? carry.lifetimeTokens : 0,
    readEver: carry ? carry.readEver : {},
    mode: carry ? carry.mode : null,
    theme: carry ? carry.theme : null,
    language: carry ? carry.language : null,
    lastSeen: Date.now()
  };
}

let S = newRun();
let currentShelf = "skills";
let openFile = null;          // { shelf, index } shown in the reader
let buyAmount = 1;            // 1, 10 or "max"
let chat = [];                // last few prompt/reply pairs
let nextPrompt = 0;           // index into the locale's prompt list

function load(hotData) {
  let data = hotData;
  if (!data) { try { const raw = localStorage.getItem(SAVE_KEY); if (raw) data = JSON.parse(raw); } catch (e) { /* storage blocked */ } }
  if (!data || data.version !== 2) return;
  const fresh = newRun();
  S = Object.assign(fresh, data);
  S.owned = Object.assign(fresh.owned, data.owned || {});
  S.setup = Object.assign(fresh.setup, data.setup || {});
  if (!Array.isArray(S.producers) || S.producers.length !== PRODUCERS.length) S.producers = fresh.producers;
}
function save() {
  S.lastSeen = Date.now();
  try { localStorage.setItem(SAVE_KEY, JSON.stringify(S)); } catch (e) { /* storage blocked */ }
}

/* ================= ECONOMY ================= */

const ownedOn = shelfId => S.owned[shelfId].filter(Boolean).length;
const ownedTotal = () => SHELVES.reduce((sum, s) => sum + ownedOn(s.id), 0);
const mode = () => MODES[S.mode] || MODES.standard;
const prestigeMultiplier = () => Math.pow(2, S.stars);
const libraryMultiplier = () => Math.pow(LIBRARY_MULTIPLIER, ownedTotal());

function milestoneMultiplier(count) {
  return PRODUCER_MILESTONES.reduce((m, threshold) => (count >= threshold ? m * 2 : m), 1);
}
function debtBrake() {
  return DEBT_BRAKE_PLUGINS.reduce((f, i) => (S.owned.plugins[i] ? f * DEBT_BRAKE_FACTOR : f), 1);
}
const debtMultiplier = () => 1 - DEBT_MAX_PENALTY * (S.debt / 100);

// Output of one unit of producer `i`, before global multipliers.
function unitRate(i) {
  return PRODUCERS[i].rate * milestoneMultiplier(S.producers[i]) * (S.owned.agents[i] ? AGENT_PRODUCER_MULTIPLIER : 1);
}
function globalMultiplier() {
  return Math.pow(PLUGIN_OUTPUT_MULTIPLIER, ownedOn("plugins")) * (1 + 0.1 * S.setup.context)
    * libraryMultiplier() * prestigeMultiplier() * mode().output * debtMultiplier();
}
function tokensPerSecond() {
  let base = 0;
  for (let i = 0; i < PRODUCERS.length; i++) base += S.producers[i] * unitRate(i);
  return base * globalMultiplier();
}
function tokensPerClick() {
  return Math.pow(2, S.setup.prompt) * Math.pow(SKILL_CLICK_MULTIPLIER, ownedOn("skills"))
    * libraryMultiplier() * prestigeMultiplier() * mode().output
    + tokensPerSecond() * 0.01 * S.setup.tab;
}

const producerPrice = (i, offset) => PRODUCERS[i].cost * Math.pow(PRODUCER_GROWTH, S.producers[i] + offset) * mode().cost;
function batchPrice(i, count) { let total = 0; for (let k = 0; k < count; k++) total += producerPrice(i, k); return total; }
function maxAffordable(i) {
  let count = 0, total = 0;
  while (count < 1000) { const p = producerPrice(i, count); if (total + p > S.budget) break; total += p; count++; }
  return count;
}
function setupPrice(id) {
  const item = SETUP.find(u => u.id === id);
  return item.cost * Math.pow(item.growth, S.setup[id]) * mode().cost;
}
const filePrice = (shelfId, i) => SHELF[shelfId].price(i) * mode().cost;
const shelfOpen = shelfId => !SHELF[shelfId].opensAt || S.runTokens >= SHELF[shelfId].opensAt || S.owned[shelfId][0] || S.stars > 0;

// Why a file can't be bought yet, or "" if it can.
function lockReason(shelfId, i) {
  if (!shelfOpen(shelfId)) return tf("ui.opensAt", format(SHELF[shelfId].opensAt));
  if (i > 0 && !S.owned[shelfId][i - 1]) return t("ui.needsPrevious");
  if (shelfId === "agents" && S.producers[i] < 1) return tf("ui.needsProducer", listText("producers", i)[0].toLowerCase());
  return "";
}
const readPower = () => READ_BASE * Math.pow(SKILL_READ_MULTIPLIER, ownedOn("skills"));
const rewritePrice = () => Math.max(50, S.budget * REWRITE_BUDGET_SHARE);

/* ================= FORMATTING ================= */

function format(n) {
  const loc = locale().numberLocale || "en-US";
  if (!isFinite(n)) return "∞";
  if (n < 10 && n % 1) return n.toLocaleString(loc, { maximumFractionDigits: 1 });
  if (n < 1e6) return Math.floor(n).toLocaleString(loc);
  const suffixes = t("suffixes");
  let k = 0;
  while (n >= 1000 && k < suffixes.length - 1) { n /= 1000; k++; }
  return n.toLocaleString(loc, { maximumFractionDigits: n < 100 ? 2 : 1 }) + " " + suffixes[k];
}
const percent = n => n.toLocaleString(locale().numberLocale || "en-US", { maximumFractionDigits: 1 });
const tokens = n => tf("tokens", format(n));
function duration(ms) {
  const s = Math.floor(ms / 1000), h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60), x = s % 60;
  return tf("duration", h, h ? String(m).padStart(2, "0") : m, m || h ? String(x).padStart(2, "0") : x);
}
const escapeHtml = text => String(text).replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
const fileName = (shelfId, i) => SHELF[shelfId].glyph + fileText(shelfId, i).name;

/* ================= ACTIONS ================= */

function spend(amount) { S.runTokens += amount; S.lifetimeTokens += amount; S.budget += amount; }

function sendPrompt(event) {
  if (!S.mode) return;
  const value = tokensPerClick();
  spend(value);
  S.clicks++;
  S.debt = Math.min(100, S.debt + DEBT_PER_CLICK * debtBrake());
  const replies = t("replies");
  let reply = replies[Math.floor(Math.random() * replies.length)];
  if (S.clicks === 1) reply = t("messages.firstReply");
  else if (S.clicks % 100 === 0) reply = tf("messages.everyHundred", format(S.clicks));
  chat.push({ prompt: t("prompts")[nextPrompt], reply, spent: value });
  if (chat.length > 5) chat.shift();
  nextPrompt = pickPrompt();
  floatText("−" + tokens(value), event);
  renderChat();
  renderAll(); // clicks must refresh meters immediately, not only on the next tick
}
function pickPrompt() {
  const count = t("prompts").length;
  let n;
  do { n = Math.floor(Math.random() * count); } while (n === nextPrompt && count > 1);
  return n;
}
function floatText(text, event) {
  const box = $("#composer"), rect = box.getBoundingClientRect(), el = document.createElement("span");
  el.className = "float";
  el.textContent = text;
  const x = event && event.clientX ? event.clientX - rect.left - 30 : rect.width - 140;
  const y = event && event.clientY ? event.clientY - rect.top - 24 : 4;
  el.style.left = Math.max(0, Math.min(rect.width - 120, x)) + "px";
  el.style.top = y + "px";
  el.style.setProperty("--dx", (Math.random() * 40 - 20) + "px");
  box.appendChild(el);
  setTimeout(() => el.remove(), 900);
}
function buyProducer(i) {
  const count = buyAmount === "max" ? maxAffordable(i) : buyAmount;
  if (count < 1) return;
  const price = batchPrice(i, count);
  if (price > S.budget) return;
  S.budget -= price;
  S.producers[i] += count;
  renderAll();
}
function buySetup(id) {
  const item = SETUP.find(u => u.id === id);
  if (S.setup[id] >= item.max) return;
  const price = setupPrice(id);
  if (price > S.budget) return;
  S.budget -= price;
  S.setup[id]++;
  renderAll();
}
function buyFile(shelfId, i) {
  if (S.owned[shelfId][i] || lockReason(shelfId, i)) return;
  const price = filePrice(shelfId, i);
  if (price > S.budget) return;
  S.budget -= price;
  S.owned[shelfId][i] = true;
  openReader(shelfId, i);
  toast(tf("messages.installed", fileName(shelfId, i)));
  if (ownedTotal() === TOTAL_FILES && !S.missionShown) {
    S.missionShown = true;
    if (S.mode === "speedrun") S.speedrunTime = Date.now() - S.startedAt;
    setTimeout(showMissionComplete, 500);
  }
  renderAll();
}
function readCode() {
  if (S.debt <= 0) { toast(t("messages.nothingToRead")); return; }
  S.debt = Math.max(0, S.debt - readPower());
  S.linesRead += 8 + Math.floor(Math.random() * 33);
  renderDebt();
}
function rewriteEverything() {
  if (S.debt < 1) return;
  const price = rewritePrice();
  if (price > S.budget) return;
  S.budget -= price;
  S.debt *= REWRITE_KEEPS;
  S.rewrites++;
  toast(t("messages.rewritten"));
  renderAll();
}

/* ================= RENDERING ================= */

function applyStaticText() {
  document.documentElement.lang = locale().code;
  $$("[data-i18n]").forEach(el => { el.textContent = t(el.dataset.i18n); });
  $$("[data-i18n-aria]").forEach(el => el.setAttribute("aria-label", t(el.dataset.i18nAria)));
  $$("[data-i18n-title]").forEach(el => el.setAttribute("title", t(el.dataset.i18nTitle)));
  $("#about-text").innerHTML = t("ui.about").map(p => "<p>" + p + "</p>").join(""); // locale HTML (only <code>)
  const select = $("#lang-select");
  select.innerHTML = Object.values(window.LOCALES).map(l => '<option value="' + escapeHtml(l.code) + '">' + escapeHtml(l.label) + "</option>").join("");
  select.value = language;
}

function renderChat() {
  const entries = chat.length ? chat : [{ system: true, reply: t("ui.sessionStart") }];
  $("#chat-log").innerHTML = entries.map(e => e.system
    ? '<div class="exchange system"><div class="ai">' + escapeHtml(e.reply) + "</div></div>"
    : '<div class="exchange"><div class="me"><span class="who">' + escapeHtml(t("ui.you")) + "</span>" + escapeHtml(e.prompt) + '</div><div class="ai">' + escapeHtml(e.reply) + '<span class="spent">−' + escapeHtml(tokens(e.spent)) + "</span></div></div>").join("");
  $("#next-prompt").textContent = t("prompts")[nextPrompt];
}

function buildLists() {
  $("#producer-list").innerHTML = PRODUCERS.map((p, i) =>
    '<button class="item" data-index="' + i + '" id="producer-' + i + '"><span class="name"><span class="nm"></span><span class="qty"></span></span><span class="price"></span><span class="sub"></span></button>').join("");
  $$("#producer-list .item").forEach(b => { b.onclick = () => buyProducer(+b.dataset.index); });
  $("#setup-list").innerHTML = SETUP.map((u, i) =>
    '<button class="item" data-id="' + u.id + '" id="setup-' + u.id + '"><span class="name"><span class="nm"></span><span class="qty"></span></span><span class="price"></span><span class="sub"></span></button>').join("");
  $$("#setup-list .item").forEach(b => { b.onclick = () => buySetup(b.dataset.id); });
}

function renderProducers() {
  const visible = i => i === 0 || S.producers[i] > 0 || S.producers[i - 1] > 0 || S.runTokens >= PRODUCERS[i].cost * 0.4;
  let shownTeaser = false;
  const global = globalMultiplier();
  PRODUCERS.forEach((p, i) => {
    const b = $("#producer-" + i);
    if (!visible(i)) {
      if (shownTeaser) { b.hidden = true; return; }
      shownTeaser = true;
      b.hidden = false; b.classList.add("unknown"); b.disabled = true; b.classList.remove("affordable");
      b.querySelector(".nm").textContent = t("ui.unreleased");
      b.querySelector(".qty").textContent = "";
      b.querySelector(".sub").textContent = tf("ui.appearsAt", format(p.cost * 0.4));
      b.querySelector(".price").textContent = "";
      return;
    }
    const [name, description] = listText("producers", i);
    b.hidden = false; b.classList.remove("unknown");
    const count = buyAmount === "max" ? Math.max(1, maxAffordable(i)) : buyAmount;
    const price = batchPrice(i, count);
    const affordable = price <= S.budget && (buyAmount !== "max" || maxAffordable(i) > 0);
    b.disabled = !affordable;
    b.classList.toggle("affordable", affordable);
    b.querySelector(".nm").textContent = name;
    b.querySelector(".qty").textContent = S.producers[i] ? "×" + S.producers[i] + (S.owned.agents[i] ? " · " + t("ui.supervised") : "") : "";
    b.querySelector(".price").textContent = (count > 1 ? count + "× · " : "") + format(price);
    b.querySelector(".sub").textContent = description + " · " + tf("ui.each", format(unitRate(i) * global));
  });
}

function renderSetup() {
  SETUP.forEach((u, i) => {
    const b = $("#setup-" + u.id), level = S.setup[u.id], price = setupPrice(u.id), maxed = level >= u.max;
    const [name, description] = listText("setup", i);
    b.disabled = maxed || price > S.budget;
    b.classList.toggle("affordable", !b.disabled);
    b.querySelector(".nm").textContent = name;
    b.querySelector(".sub").textContent = description;
    b.querySelector(".qty").textContent = u.max < Infinity ? tf("ui.levelOf", level, u.max) : tf("ui.level", level);
    b.querySelector(".price").textContent = maxed ? t("ui.maxed") : format(price);
  });
}

function renderDebt() {
  $("#debt-percent").textContent = percent(S.debt) + "%";
  $("#debt-fill").style.width = S.debt + "%";
  $("#debt-bar").classList.toggle("high", S.debt >= 60);
  $("#debt-effect").textContent = tf("ui.agentsYield", Math.round(debtMultiplier() * 100));
  $("#read-cost").textContent = tf("ui.readCost", percent(readPower()));
  const price = rewritePrice();
  $("#rewrite-cost").textContent = tf("ui.rewriteCost", format(price));
  $("#rewrite-button").disabled = S.debt < 1 || price > S.budget;
}

function renderHeader() {
  $("#meter-spent").textContent = format(S.runTokens);
  $("#meter-budget").textContent = format(S.budget);
  const rate = tokensPerSecond();
  $("#meter-rate").textContent = rate > 0 ? tf("ui.perSecond", format(rate)) : "";
  let tier = 0;
  TIER_THRESHOLDS.forEach((threshold, i) => { if (S.runTokens >= threshold) tier = i; });
  const position = Math.max(1, Math.round(4000 * Math.exp(-Math.log10(S.runTokens + 1) / 1.6)));
  $("#meter-tier").innerHTML = tf("ui.leaderboard", position.toLocaleString(locale().numberLocale), escapeHtml(listText("tiers", tier)));
  const badge = $("#meter-mode");
  if (S.mode === "hardcore") { badge.hidden = false; badge.textContent = t("ui.hardcore"); }
  else if (S.mode === "speedrun") { badge.hidden = false; badge.textContent = tf("ui.speedrun", duration(S.speedrunTime ?? (Date.now() - S.startedAt))); }
  else badge.hidden = true;
  $("#stars").textContent = S.stars ? "★×" + S.stars : "";
  $("#click-value").textContent = tokens(tokensPerClick());
  $("#stat-prompts").textContent = format(S.clicks);
  $("#stat-multiplier").textContent = "×" + (libraryMultiplier() * prestigeMultiplier()).toLocaleString(locale().numberLocale, { maximumFractionDigits: 2 });
  $("#stat-agents").textContent = format(S.producers.reduce((a, b) => a + b, 0));
  $("#library-count").textContent = ownedTotal() + "/" + TOTAL_FILES;
  const unread = SHELVES.some(s => S.owned[s.id].some((own, i) => own && !S.readThisRun[s.id + i]));
  const buyable = SHELVES.some(s => S.owned[s.id].some((own, i) => !own && !lockReason(s.id, i) && filePrice(s.id, i) <= S.budget));
  $("#library-dot").hidden = !(unread || buyable);
}

function renderLibrary() {
  SHELVES.forEach(s => { $("#shelf-count-" + s.id).textContent = ownedOn(s.id) + "/" + FILES_PER_SHELF; });
  $$(".shelves button").forEach(b => b.setAttribute("aria-pressed", b.dataset.shelf === currentShelf));
  const shelf = SHELF[currentShelf];
  $("#shelf-hint").textContent = shelfOpen(currentShelf) ? t("shelves." + currentShelf + ".hint") : tf("ui.shelfLocked", format(shelf.opensAt));
  const html = Array.from({ length: FILES_PER_SHELF }, (_, i) => {
    const owned = S.owned[currentShelf][i], reason = lockReason(currentShelf, i), price = filePrice(currentShelf, i);
    const readBefore = S.readEver[currentShelf + i];
    let cls = "file", status;
    if (owned) status = S.readThisRun[currentShelf + i] ? t("ui.statusRead") : t("ui.statusOpen");
    else if (reason) { cls += " locked"; status = readBefore ? tf("ui.readBefore", reason) : reason; }
    else { cls += " buyable" + (price > S.budget ? " pricey" : ""); status = format(price); }
    const name = owned || readBefore || !reason ? fileName(currentShelf, i) : shelf.glyph + "•••••••";
    const dot = owned && !S.readThisRun[currentShelf + i] ? '<span class="unread" aria-label="' + escapeHtml(t("ui.unread")) + '"></span>' : "";
    const current = openFile && openFile.shelf === currentShelf && openFile.index === i;
    return '<button class="' + cls + '" data-index="' + i + '"' + (current ? ' aria-current="true"' : "") + '><span class="glyph">' + String(i + 1).padStart(2, "0") +
      '</span><span class="title">' + escapeHtml(name) + dot + '</span><span class="status">' + escapeHtml(status) + "</span></button>";
  }).join("");
  const list = $("#file-list");
  if (list.dataset.html !== html) {   // rebuild only when something changed, so clicks aren't lost
    list.innerHTML = html;
    list.dataset.html = html;
    $$("#file-list .file").forEach(b => { b.onclick = () => clickFile(+b.dataset.index); });
  }
}
function clickFile(i) {
  const shelfId = currentShelf;
  if (S.owned[shelfId][i] || (S.readEver[shelfId + i] && lockReason(shelfId, i))) openReader(shelfId, i);
  else if (!lockReason(shelfId, i)) {
    if (filePrice(shelfId, i) <= S.budget) buyFile(shelfId, i);
    else toast(tf("messages.notEnough", fileName(shelfId, i), format(filePrice(shelfId, i))));
  }
}
function effectText(shelfId, i) {
  if (shelfId === "agents") return tf("shelves.agents.effect", listText("producers", i)[0]);
  if (shelfId === "plugins" && DEBT_BRAKE_PLUGINS.includes(i)) return t("shelves.plugins.effect") + " · " + t("shelves.plugins.brake");
  return t("shelves." + shelfId + ".effect");
}
function openReader(shelfId, i) {
  openFile = { shelf: shelfId, index: i };
  const text = fileText(shelfId, i), shelf = SHELF[shelfId];
  if (S.owned[shelfId][i]) { S.readThisRun[shelfId + i] = true; S.readEver[shelfId + i] = true; }
  const source = S.owned[shelfId][i] ? t("ui.installedThisRun") : t("ui.readInPreviousRun");
  $("#reader").innerHTML =
    '<div class="file-bar"><span>' + shelf.id + "/" + escapeHtml(text.name) + "/" + shelf.file + "</span><span>" + escapeHtml(source) + "</span></div>" +
    '<pre><span class="label">---</span>\n<span class="label">name:</span> <span class="value">' + escapeHtml(text.name) +
    '</span>\n<span class="label">type:</span> <span class="value">' + shelf.type +
    '</span>\n<span class="label">description:</span> <span class="value">' + escapeHtml(text.description) +
    '</span>\n<span class="label">effect:</span> <span class="effect">' + escapeHtml(effectText(shelfId, i)) +
    '</span>\n<span class="label">---</span></pre>' +
    "<article><h3>" + escapeHtml(shelf.glyph + text.name) + "</h3>" + text.body.map(p => "<p>" + escapeHtml(p) + "</p>").join("") +
    (text.comment ? '<p class="comment">&lt;!-- ' + escapeHtml(text.comment) + " --&gt;</p>" : "") + "</article>";
  currentShelf = shelfId;
  renderLibrary();
  renderHeader();
  if (window.matchMedia("(max-width:860px)").matches) $("#reader").scrollIntoView({ behavior: "smooth", block: "start" });
}
function renderReadme() {
  openFile = null;
  $("#reader").innerHTML = '<div class="file-bar"><span>library/README.md</span><span>' + escapeHtml(t("ui.alwaysAvailable")) + "</span></div>" +
    '<div class="empty">' + t("ui.readme").map(p => "<p>" + escapeHtml(p) + "</p>").join("") +
    '<p style="color:var(--muted);font-family:var(--mono);font-size:12.5px">' + escapeHtml(tf("ui.readmeFirst", fileName("skills", 0), format(filePrice("skills", 0)))) + "</p></div>";
}

function renderStats() {
  const stat = key => t("ui.stats." + key);
  const rows = [
    [stat("runTokens"), format(S.runTokens)],
    [stat("allTokens"), format(S.lifetimeTokens)],
    [stat("prompts"), format(S.clicks)],
    [stat("linesRead"), format(S.linesRead)],
    [stat("rewrites"), format(S.rewrites)],
    [stat("agents"), format(S.producers.reduce((a, b) => a + b, 0))],
    [stat("library"), tf("ui.ofTotal", ownedTotal(), TOTAL_FILES)],
    [stat("textsRead"), tf("ui.ofTotal", Object.keys(S.readEver).length, TOTAL_FILES)],
    [stat("debt"), percent(S.debt) + "%"],
    [stat("apiBill"), tf("ui.money", format(S.lifetimeTokens * 0.00004))],
    [stat("water"), tf("ui.liters", format(S.lifetimeTokens * 0.0003))],
    [stat("playTime"), duration(S.playSeconds * 1000)],
    [stat("clears"), format(S.stars)]
  ];
  $("#stats-table").innerHTML = rows.map(r => "<tr><td>" + escapeHtml(r[0]) + "</td><td>" + escapeHtml(r[1]) + "</td></tr>").join("");
  const missing = TOTAL_FILES - ownedTotal();
  $("#clear-note").textContent = missing ? tf("ui.clearLocked", missing) : tf("ui.clearReady", Math.pow(2, S.stars + 1));
  $("#clear-button").disabled = missing > 0;
}

function renderAll() {
  renderHeader(); renderProducers(); renderSetup(); renderDebt(); renderLibrary();
  if (!$("#panel-about").hidden) renderStats();
}

/* ================= DIALOGS ================= */

// buttons: [{ label, style, onClick }]. `onClose` adds an X button.
function showDialog({ title, subtitle, html, reading, buttons, onClose, beforeBody }) {
  const dialog = $("#dialog");
  dialog.innerHTML = (onClose ? '<button class="close" id="dialog-close" aria-label="' + escapeHtml(t("dialogs.close")) + '">✕</button>' : "") +
    '<h2 id="dialog-title">' + escapeHtml(title) + "</h2>" + (subtitle ? '<p class="sub">' + escapeHtml(subtitle) + "</p>" : "") +
    (beforeBody || "") + '<div class="body' + (reading ? " reading" : "") + '">' + html + '</div><div class="buttons" id="dialog-buttons"></div>';
  (buttons || []).forEach(b => {
    const el = document.createElement("button");
    el.className = "btn" + (b.style ? " " + b.style : "");
    el.textContent = b.label;
    el.onclick = () => { closeDialog(); if (b.onClick) b.onClick(); };
    $("#dialog-buttons").appendChild(el);
  });
  if (onClose) $("#dialog-close").onclick = () => { closeDialog(); onClose(); };
  $("#overlay").hidden = false;
  const focus = dialog.querySelector(".buttons .btn:last-child") || dialog.querySelector("button");
  if (focus) focus.focus();
}
function closeDialog() { $("#overlay").hidden = true; }

let toastTimer;
function toast(text) {
  const el = $("#toast");
  el.textContent = text;
  el.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { el.hidden = true; }, 3800);
}

function languageOptions() {
  return '<select class="lang" id="dialog-lang" aria-label="' + escapeHtml(t("ui.language")) + '">' +
    Object.values(window.LOCALES).map(l => '<option value="' + escapeHtml(l.code) + '"' + (l.code === language ? " selected" : "") + ">" + escapeHtml(l.label) + "</option>").join("") + "</select>";
}
function showTerms() {
  showDialog({
    title: t("dialogs.termsTitle"),
    subtitle: t("dialogs.termsSub"),
    beforeBody: languageOptions(),
    html: "<ol>" + t("dialogs.terms").map(term => "<li><b>" + escapeHtml(term[0]) + ".</b> " + escapeHtml(term[1]) + "</li>").join("") + "</ol>",
    buttons: [
      { label: t("dialogs.decline"), onClick: () => chooseMode("hardcore") },
      { label: t("dialogs.accept"), style: "primary", onClick: () => chooseMode("standard") }
    ],
    onClose: () => chooseMode("speedrun")
  });
  $("#dialog-lang").onchange = e => { setLanguage(e.target.value); showTerms(); };
}
function chooseMode(chosen) {
  S = newRun(Object.assign({}, S, { mode: chosen }));
  toast(t("messages.modes." + chosen));
  chat = [];
  renderChat(); renderAll(); save();
}
function showMissionComplete() {
  showDialog({
    title: t("dialogs.missionTitle"),
    html: "<p>" + escapeHtml(t("dialogs.missionText")) + "</p>" + (S.speedrunTime ? "<p>" + escapeHtml(tf("dialogs.speedrunTime", duration(S.speedrunTime))) + "</p>" : ""),
    buttons: [{ label: t("dialogs.later") }, { label: t("ui.runClear"), style: "primary", onClick: confirmClear }]
  });
}
function confirmClear() {
  if (ownedTotal() < TOTAL_FILES) return;
  showDialog({
    title: t("dialogs.clearConfirmTitle"),
    html: "<p>" + escapeHtml(tf("dialogs.clearConfirmText", Math.pow(2, S.stars + 1))) + "</p>",
    buttons: [{ label: t("dialogs.keep") }, { label: t("dialogs.clearIt"), style: "primary", onClick: runClear }]
  });
}
function runClear() {
  S = newRun({ stars: S.stars + 1, lifetimeTokens: S.lifetimeTokens, readEver: S.readEver, mode: S.mode, theme: S.theme, language: S.language });
  chat = []; currentShelf = "skills";
  renderReadme(); renderChat(); renderAll(); save();
  showDialog({
    title: t("dialogs.clearedTitle"), reading: true,
    html: t("dialogs.clearedText").map(p => "<p>" + escapeHtml(p) + "</p>").join("") +
      '<p class="contribute">' + escapeHtml(t("dialogs.contribute")) + ' <a href="' + REPOSITORY_URL + '" target="_blank" rel="noopener">' + REPOSITORY_URL.replace("https://", "") + "</a></p>",
    buttons: [{ label: tf("dialogs.startWith", prestigeMultiplier()), style: "primary" }]
  });
}
function confirmMasterReset() {
  showDialog({
    title: t("dialogs.masterConfirmTitle"),
    html: "<p>" + escapeHtml(t("dialogs.masterConfirmText")) + "</p>",
    buttons: [{ label: t("dialogs.keep") }, {
      label: t("dialogs.eraseIt"), style: "danger", onClick: () => {
        try { localStorage.removeItem(SAVE_KEY); } catch (e) { /* storage blocked */ }
        const keep = { theme: S.theme, language: S.language };
        S = Object.assign(newRun(), keep);
        chat = []; currentShelf = "skills";
        renderReadme(); renderChat(); renderAll(); showTerms();
      }
    }]
  });
}

/* ================= TABS, THEME, LANGUAGE ================= */

function showPanel(id) {
  $$(".tab").forEach(tab => tab.setAttribute("aria-selected", tab.dataset.panel === id));
  ["prompt", "library", "about"].forEach(p => { $("#panel-" + p).hidden = p !== id; });
  if (id === "about") renderStats();
  if (id === "library") renderLibrary();
}
function applyTheme() {
  if (S.theme) document.documentElement.setAttribute("data-theme", S.theme);
  else document.documentElement.removeAttribute("data-theme");
}
function setLanguage(code) {
  language = window.LOCALES[code] ? code : DEFAULT_LANGUAGE;
  S.language = language;
  applyStaticText();
  nextPrompt = Math.min(nextPrompt, t("prompts").length - 1);
  renderChat();
  if (openFile) openReader(openFile.shelf, openFile.index); else renderReadme();
  renderAll();
  save();
}

/* ================= MAIN LOOP ================= */

let lastFrame = performance.now(), frame = 0;
const debtWarned = {};
function tick() {
  const now = performance.now(), dt = Math.min(1, (now - lastFrame) / 1000);
  lastFrame = now;
  if (S.mode) {
    const rate = tokensPerSecond();
    if (rate > 0) spend(rate * dt);
    const types = S.producers.filter(n => n > 0).length;
    S.debt = Math.min(100, S.debt + DEBT_PER_PRODUCER_TYPE_PER_SECOND * types * debtBrake() * dt);
    S.playSeconds += dt;
    [50, 80, 100].forEach(level => {
      if (S.debt >= level && !debtWarned[level]) { debtWarned[level] = true; toast(t("messages.debt." + level)); }
      if (S.debt < level - 10) debtWarned[level] = false;
    });
  }
  frame++;
  renderHeader(); renderDebt();
  if (frame % 3 === 0) { renderProducers(); renderSetup(); if (!$("#panel-library").hidden) renderLibrary(); }
  if (frame % 10 === 0 && !$("#panel-about").hidden) renderStats();
  if (frame % 50 === 0) save();
}

function applyOfflineProgress() {
  const away = Math.min(OFFLINE_CAP_SECONDS, (Date.now() - (S.lastSeen || Date.now())) / 1000);
  const rate = tokensPerSecond();
  if (away <= 60 || rate <= 0) return;
  const gain = rate * away * OFFLINE_EFFICIENCY;
  spend(gain);
  const types = S.producers.filter(n => n > 0).length;
  S.debt = Math.min(100, S.debt + DEBT_PER_PRODUCER_TYPE_PER_SECOND * types * debtBrake() * away);
  setTimeout(() => toast(tf("messages.offline", format(gain), Math.round(S.debt))), 600);
}

function start(hotData) {
  load(hotData && hotData.state);
  language = window.LOCALES[S.language] ? S.language : DEFAULT_LANGUAGE;
  applyTheme();
  applyStaticText();
  nextPrompt = pickPrompt();
  buildLists();
  renderChat();
  renderReadme();
  if (S.mode && !hotData) applyOfflineProgress();

  $("#send-button").onclick = sendPrompt;
  $("#read-button").onclick = readCode;
  $("#rewrite-button").onclick = rewriteEverything;
  $("#clear-button").onclick = confirmClear;
  $("#master-button").onclick = confirmMasterReset;
  $("#lang-select").onchange = e => setLanguage(e.target.value);
  $$(".tab").forEach(tab => { tab.onclick = () => showPanel(tab.dataset.panel); });
  $$(".amount button").forEach(b => {
    b.onclick = () => {
      buyAmount = b.dataset.amount === "max" ? "max" : +b.dataset.amount;
      $$(".amount button").forEach(x => x.setAttribute("aria-pressed", x === b));
      renderProducers();
    };
  });
  $$(".shelves button").forEach(b => { b.onclick = () => { currentShelf = b.dataset.shelf; renderLibrary(); }; });
  $("#theme-toggle").onclick = () => {
    const darkNow = S.theme ? S.theme === "dark" : matchMedia("(prefers-color-scheme: dark)").matches;
    S.theme = darkNow ? "light" : "dark";
    applyTheme();
    save();
  };
  // Enter or Space sends a prompt when focus isn't on another control.
  document.addEventListener("keydown", e => {
    if (!$("#overlay").hidden || $("#panel-prompt").hidden) return;
    if ((e.key === "Enter" || e.key === " ") && (document.activeElement === document.body || !document.activeElement)) {
      e.preventDefault();
      if (!e.repeat) sendPrompt();
    }
  });
  document.addEventListener("visibilitychange", () => { if (document.hidden) save(); });
  window.addEventListener("pagehide", save);

  renderAll();
  if (!S.mode) showTerms();
  setInterval(tick, TICK_MS);
}

// Keeps state across live reloads when hosted as a Claude artifact; harmless elsewhere.
if (window.claude?.hot?.snapshot) window.claude.hot.snapshot(() => ({ state: S }));
if (window.claude?.hot?.ready) window.claude.hot.ready(start);
else start(window.claude?.hot?.data ?? null);
