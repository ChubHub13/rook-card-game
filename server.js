const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = Number(process.env.PORT || 8080);
const HOST = process.env.HOST || '0.0.0.0';
const PUBLIC_DIR = __dirname;
const VERSION = '1.1.40';
const PLAYER_NAMES = ['Daryl', 'Cristi', 'Cindy'];
const SUITS = ['red', 'yellow', 'green', 'black'];
const VALUES = [1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
const WIN_SCORE = 1000;
const BID_START = 150;
const KITTY_SIZE = 9;
const HAND_SIZE = 12;
const PLAYER_TIMEOUT_MS = 8000;
const TRICK_REVEAL_MS = 3000;
const TRUMP_REVEAL_MS = 5000;
const BOT_DELAY = { bid: 650, play: 550, trick: 850 };

const sessions = new Map();
let botTimer = null;
let revealTimer = null;

function makeId(prefix = '') { return prefix + crypto.randomBytes(10).toString('hex'); }
function cleanName(value) { const v = String(value || '').trim(); return PLAYER_NAMES.includes(v) ? v : null; }
function now() { return Date.now(); }
function clamp(v, min, max) { return Math.max(min, Math.min(max, v)); }

const game = {
  version: VERSION,
  phase: 'waiting',
  handNumber: 0,
  dealer: 0,
  currentBidder: 0,
  highBid: 0,
  highBidder: null,
  lastBidderName: '',
  bidHistory: [],
  passed: [false, false, false],
  hands: [[], [], []],
  kitty: [],
  kittyAccepted: false,
  selectedDiscards: [],
  trump: null,
  trick: [],
  lastTrick: null,
  revealUntil: 0,
  leader: 0,
  turn: 0,
  scores: [0, 0, 0],
  botBidSetCounts: [0, 0, 0],
  botBidBlockedThroughHand: [0, 0, 0],
  handPoints: [0, 0, 0],
  tricksWon: [0, 0, 0],
  playedCards: [],
  playHistory: [],
  humanSeatsThisHand: [false, false, false],
  lastHandResult: null,
  started: false,
  winner: null,
  live: [false, false, false],
  bot: [true, true, true],
  lastSeen: [0, 0, 0],
  chat: [],
  claimReveal: null,
  bitterVotes: [false, false, false],
  misdealSeats: [],
  prompt: 'Choose a player to begin.',
};

function buildDeck() {
  let id = 0;
  const deck = [];
  for (const suit of SUITS) for (const value of VALUES) deck.push({ id: `c${id++}`, suit, value, rook: false });
  deck.push({ id: `c${id++}`, suit: 'rook', value: null, rook: true });
  return deck;
}
function shuffle(deck) {
  for (let i = deck.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [deck[i], deck[j]] = [deck[j], deck[i]];
  }
  return deck;
}
function cardPoints(card) {
  if (card.rook) return 20;
  if (card.value === 1) return 15;
  if (card.value === 5) return 5;
  if (card.value === 10 || card.value === 14) return 10;
  return 0;
}
function cardRank(card) { return card.rook ? 10.5 : card.value === 1 ? 15 : card.value; }
function effectiveSuit(card) {
  if (!card.rook) return card.suit;
  return game.trump === 'none' ? 'red' : game.trump;
}
function cardName(card) { return card.rook ? 'the Rook' : `${card.suit} ${card.value}`; }
function playerName(seat) { return PLAYER_NAMES[seat]; }

function sortHand(hand) {
  const suitOrder = { red: 0, yellow: 1, green: 2, black: 3, rook: 4 };
  hand.sort((a, b) => {
    const sa = a.rook && game.trump ? effectiveSuit(a) : (a.rook ? 'rook' : a.suit);
    const sb = b.rook && game.trump ? effectiveSuit(b) : (b.rook ? 'rook' : b.suit);
    const suitDiff = (suitOrder[sa] ?? 9) - (suitOrder[sb] ?? 9);
    if (suitDiff) return suitDiff;
    return cardRank(b) - cardRank(a);
  });
}

function resetGame() {
  clearTimeout(botTimer); clearTimeout(revealTimer);
  for (let i = 0; i < 3; i++) { game.live[i] = false; game.bot[i] = true; game.lastSeen[i] = 0; }
  game.phase = 'waiting'; game.handNumber = 0; game.dealer = 0; game.currentBidder = 0;
  game.highBid = 0; game.highBidder = null; game.lastBidderName = ''; game.bidHistory = [];
  game.passed = [false, false, false]; game.hands = [[], [], []]; game.kitty = []; game.kittyAccepted = false;
  game.selectedDiscards = []; game.trump = null; game.trick = []; game.lastTrick = null; game.revealUntil = 0;
  game.leader = 0; game.turn = 0; game.scores = [0, 0, 0]; game.botBidSetCounts = [0, 0, 0]; game.botBidBlockedThroughHand = [0, 0, 0]; game.handPoints = [0, 0, 0]; game.tricksWon = [0, 0, 0]; game.playedCards = []; game.playHistory = [];
  game.started = false; game.winner = null; game.chat = []; game.claimReveal = null; game.bitterVotes = [false, false, false]; game.humanSeatsThisHand = [false, false, false]; game.prompt = 'Choose a player to begin.';
}

function ensureBots() {
  for (let i = 0; i < 3; i++) if (!game.live[i]) game.bot[i] = true;
}

function createDeal() {
  let deck = shuffle(buildDeck());
  game.hands = [[], [], []];
  for (let round = 0; round < HAND_SIZE; round++) {
    for (let offset = 1; offset <= 3; offset++) game.hands[(game.dealer + offset) % 3].push(deck.pop());
  }
  game.kitty = deck.splice(0);
  game.hands.forEach(sortHand);
}

function resetHand() {
  clearTimeout(botTimer); clearTimeout(revealTimer);
  game.handNumber += 1;
  game.dealer = game.handNumber === 1 ? game.dealer : (game.dealer + 1) % 3;
  game.currentBidder = (game.dealer + 1) % 3;
  game.phase = 'bidding';
  game.highBid = 0; game.highBidder = null; game.lastBidderName = ''; game.bidHistory = []; game.passed = [false, false, false];
  game.trump = null; game.kittyAccepted = false; game.selectedDiscards = []; game.bitterVotes = [false, false, false]; game.trick = []; game.revealUntil = 0;
  game.handPoints = [0, 0, 0]; game.tricksWon = [0, 0, 0]; game.playedCards = []; game.playHistory = []; game.lastHandResult = null; game.claimReveal = null; game.winner = null;
  game.humanSeatsThisHand = game.bot.map(isBot => !isBot);
  createDeal();
  game.misdealSeats = game.hands.map((hand, seat) => hand.reduce((total, card) => total + cardPoints(card), 0) === 0 ? seat : -1).filter(seat => seat >= 0);
  game.prompt = `${playerName(game.currentBidder)} bids first.`;
  scheduleBotBidIfNeeded();
}

function minLegalBid() {
  if (!game.highBid) return BID_START;
  if (game.highBid < 200) return game.highBid + 5;
  if (game.highBid < 400) return 400;
  return 401;
}

function analyzeBotBidHand(hand) {
  const hasRook = hand.some(c => c.rook);
  const aces = hand.filter(c => !c.rook && c.value === 1).length;
  const suitCounts = Object.fromEntries(SUITS.map(s => [s, hand.filter(c => !c.rook && c.suit === s).length]));
  const suitScore = suit => hand.reduce((score, card) => {
    if (card.rook) return score + 9;
    if (card.suit !== suit) return score;
    if (card.value === 1) return score + 20;
    if (card.value === 14) return score + 12;
    if (card.value === 13) return score + 8;
    if (card.value === 12) return score + 5;
    return score + 2 + cardPoints(card) * 0.25;
  }, suitCounts[suit] * 11);
  const bestTrump = SUITS.reduce((best, s) => suitScore(s) > suitScore(best) ? s : best, SUITS[0]);
  const potentialTrumpCount = suitCounts[bestTrump] + (hasRook ? 1 : 0);
  const covered = new Set();
  const standard = [1, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5];
  const trumpOrder = [1, 14, 13, 12, 11, 'rook', 10, 9, 8, 7, 6, 5];
  function markRun(suit, order) {
    for (const rank of order) {
      const c = rank === 'rook' ? hand.find(x => x.rook) : hand.find(x => !x.rook && x.suit === suit && x.value === rank);
      if (!c) break;
      covered.add(c.id);
    }
  }
  for (const s of SUITS) markRun(s, s === bestTrump ? trumpOrder : standard);
  return { hasRook, aces, bestTrump, potentialTrumpCount, fullCoverage: covered.size === hand.length };
}

function estimateMaxBid(hand) {
  const strength = analyzeBotBidHand(hand);
  const suitCards = Object.fromEntries(SUITS.map(s => [s, hand.filter(c => !c.rook && c.suit === s)]));
  const scoreSuit = s => (suitCards[s].length + (strength.hasRook ? 1 : 0)) * 7 + suitCards[s].reduce((n, c) => n + (c.value === 1 ? 8 : c.value === 14 ? 6 : c.value >= 13 ? 3 : c.value >= 11 ? 1 : 0), 0);
  const ranked = [...SUITS].sort((a, b) => scoreSuit(b) - scoreSuit(a));
  const trumpSuit = ranked[0];
  const trumpCards = suitCards[trumpSuit];
  const trumpCount = trumpCards.length + (strength.hasRook ? 1 : 0);
  const trumpHasOne = trumpCards.some(c => c.value === 1);
  const trumpHasFourteen = trumpCards.some(c => c.value === 14);
  const totalOnes = hand.filter(c => !c.rook && c.value === 1).length;
  const topCards = hand.filter(c => !c.rook && (c.value === 1 || c.value === 14)).length;
  const secondaryOnes = hand.filter(c => !c.rook && c.suit !== trumpSuit && c.value === 1).length;
  const secondaryFourteens = hand.filter(c => !c.rook && c.suit !== trumpSuit && c.value === 14).length;
  const activeColors = SUITS.filter(s => suitCards[s].length).length;
  const voids = 4 - activeColors;
  let ref = 0;
  if (trumpCount >= 4) ref += 5;
  if (trumpCount >= 5) ref += 5;
  if (trumpCount >= 6) ref += 5;
  if (trumpCount >= 7) ref += 5;
  if (trumpHasOne) ref += 6; else if (trumpCount >= 6) ref -= 5; else ref -= 3;
  if (trumpHasFourteen) ref += 4;
  if (trumpCards.some(c => c.value === 13)) ref += 2;
  if (strength.hasRook) ref += 6;
  ref += secondaryOnes * 5 + secondaryFourteens * 2;
  for (const s of SUITS) {
    if (s === trumpSuit) continue;
    const vals = suitCards[s].map(c => c.value);
    if (vals.includes(1) && vals.includes(14)) ref += 5;
  }
  ref += voids * 3;
  if (activeColors <= 2) ref += 3;
  if (activeColors === 4) ref -= 3;
  const pts = hand.reduce((n, c) => n + cardPoints(c), 0);
  if (pts >= 45) ref += 2;
  if (pts >= 60) ref += 2;
  if ((suitCards[ranked[1]] || []).length >= 4) ref += 3;
  let estimate = Math.round((145 + ref * 0.65) / 5) * 5;
  estimate = Math.max(150, estimate);
  if (topCards >= 3 && estimate < 160) estimate = 160;
  const exceptional = trumpCount >= 8 && (trumpHasOne || strength.hasRook) && totalOnes >= 2;
  estimate = Math.min(estimate, exceptional ? 175 : 170);
  if (strength.fullCoverage) estimate = 200;
  if (estimate < 200 && Math.random() < 0.35) estimate += Math.random() < 0.5 ? -5 : 5;
  return clamp(Math.round(estimate / 5) * 5, 145, strength.fullCoverage ? 200 : 175);
}

function chooseBestTrump(hand) {
  let best = SUITS[0], bestScore = -Infinity;
  for (const suit of SUITS) {
    let score = 0;
    for (const c of hand) {
      if (c.rook) score += 10;
      else if (c.suit === suit) {
        score += 3;
        if (c.value === 1) score += 18;
        else if (c.value === 14) score += 10;
        else if (c.value === 13) score += 6;
        else if (c.value >= 11) score += 3;
        score += cardPoints(c) * 0.25;
      }
    }
    if (score > bestScore) { bestScore = score; best = suit; }
  }
  return best;
}

function discardDesirability(card, trump) {
  if (card.rook) return 100;
  let keep = cardRank(card) * 1.2 + cardPoints(card) * 2.4;
  if (card.suit === trump) keep += 20;
  if (card.value === 1) keep += 28;
  if (card.value === 14) keep += 12;
  return keep;
}
function chooseBotDiscards(hand, trump) {
  const keepCount = Math.max(0, hand.length - KITTY_SIZE);
  const winnerIds = botDiscardWinnerIds(hand, trump);
  const activeSuits = SUITS.filter(suit => hand.some(card => botDiscardSuit(card, trump) === suit));
  const sideSuits = activeSuits.filter(suit => suit !== trump);
  const corePlans = sideSuits.length
    ? sideSuits.map(suit => new Set([trump, suit]))
    : [new Set([trump])];
  let bestPlan = null;

  for (const coreSuits of corePlans) {
    const ranked = [...hand].sort((a, b) => {
      const difference = botDiscardKeepScore(b, trump, coreSuits, winnerIds)
        - botDiscardKeepScore(a, trump, coreSuits, winnerIds);
      return difference || cardRank(b) - cardRank(a) || String(a.id).localeCompare(String(b.id));
    });
    const keptIds = new Set(ranked.slice(0, keepCount).map(card => card.id));
    const discards = hand.filter(card => !keptIds.has(card.id));
    const kept = hand.filter(card => keptIds.has(card.id));
    const offCoreLosers = kept.filter(card => !coreSuits.has(botDiscardSuit(card, trump)) && !winnerIds.has(card.id)).length;
    const structuralSuits = new Set(kept.filter(card => !winnerIds.has(card.id)).map(card => botDiscardSuit(card, trump)));
    const score = kept.reduce((sum, card) => sum + discardDesirability(card, trump), 0)
      + kept.filter(card => winnerIds.has(card.id)).length * 180
      - offCoreLosers * 1000
      - Math.max(0, structuralSuits.size - 2) * 1200;
    if (!bestPlan || score > bestPlan.score) bestPlan = { score, discards };
  }

  const discards = bestPlan ? bestPlan.discards : [...hand]
    .sort((a, b) => discardDesirability(a, trump) - discardDesirability(b, trump))
    .slice(0, KITTY_SIZE);
  return avoidBadSingletonKeeps(hand, discards, trump);
}

function avoidBadSingletonKeeps(hand, discards, trump) {
  const result = [...discards];
  const discardIds = new Set(result.map(card => card.id));
  const kept = () => hand.filter(card => !discardIds.has(card.id));
  for (const suit of SUITS) {
    if (suit === trump) continue;
    const suitKept = kept().filter(card => botDiscardSuit(card, trump) === suit);
    if (suitKept.length !== 1 || suitKept[0].rook || ![10, 14].includes(suitKept[0].value)) continue;
    const badKeep = suitKept[0];
    let replacement = result.find(card => botDiscardSuit(card, trump) === suit && !card.rook && ![10, 14].includes(card.value));
    if (!replacement) {
      const populated = new Set(kept().map(card => botDiscardSuit(card, trump)));
      replacement = result.find(card => populated.has(botDiscardSuit(card, trump)) && card.id !== badKeep.id);
    }
    if (!replacement) continue;
    const index = result.findIndex(card => card.id === replacement.id);
    result[index] = badKeep;
    discardIds.delete(replacement.id);
    discardIds.add(badKeep.id);
  }
  return result;
}

function botDiscardSuit(card, trump) {
  return card.rook ? (trump === 'none' ? 'red' : trump) : card.suit;
}

function botDiscardWinnerIds(hand, trump) {
  const winners = new Set();
  const standard = [1, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5];
  for (const suit of SUITS) {
    const order = suit === trump ? [1, 14, 13, 12, 11, 'rook', 10, 9, 8, 7, 6, 5] : standard;
    for (const rank of order) {
      const card = rank === 'rook'
        ? hand.find(item => item.rook && botDiscardSuit(item, trump) === suit)
        : hand.find(item => !item.rook && item.suit === suit && item.value === rank);
      if (!card) break;
      winners.add(card.id);
    }
  }
  return winners;
}

function botDiscardKeepScore(card, trump, coreSuits, winnerIds) {
  const suit = botDiscardSuit(card, trump);
  let score = discardDesirability(card, trump);
  if (coreSuits.has(suit)) score += 90;
  if (trump !== 'none' && suit === trump) score += 45;
  if (winnerIds.has(card.id)) score += 260;
  if (card.rook) score += 80;
  if (trump !== 'none' && suit !== trump && !winnerIds.has(card.id) && !card.rook && (card.value === 10 || card.value === 5)) score -= 65;
  return score;
}

function legalCards(seat) {
  const hand = game.hands[seat] || [];
  if (!game.trick.length) return hand.slice();
  const lead = effectiveSuit(game.trick[0].card);
  const following = hand.filter(c => effectiveSuit(c) === lead);
  return following.length ? following : hand.slice();
}
function beats(challenger, incumbent, leadSuit) {
  const cs = effectiveSuit(challenger), is = effectiveSuit(incumbent);
  const ct = game.trump && game.trump !== 'none' && cs === game.trump;
  const it = game.trump && game.trump !== 'none' && is === game.trump;
  if (ct !== it) return ct;
  if (cs === is) return cardRank(challenger) > cardRank(incumbent);
  if (cs === leadSuit && is !== leadSuit) return true;
  return false;
}
function trickWinner(trick) {
  const lead = effectiveSuit(trick[0].card);
  let best = trick[0];
  for (let i = 1; i < trick.length; i++) if (beats(trick[i].card, best.card, lead)) best = trick[i];
  return best.seat;
}
function isGuarded14(card) { return !card.rook && card.value === 14 && !cardAlreadyPlayed(card.suit, 1); }
function cardAlreadyPlayed(suit, value) {
  return game.playedCards.some(c => !c.rook && c.suit === suit && c.value === value);
}
function teamOf(seat) { return seat === game.highBidder ? 0 : 1; }
function opponentsStillHoldTrump(seat) {
  if (!game.trump || game.trump === 'none') return false;
  return [0, 1, 2].some(i => i !== seat && teamOf(i) !== teamOf(seat) && game.hands[i].some(c => effectiveSuit(c) === game.trump));
}
function cardWinLooksSecure(seat, card, leadSuit) {
  const playedSeats = new Set(game.trick.map(play => play.seat));
  for (let next = (seat + 1) % 3; next !== game.leader; next = (next + 1) % 3) {
    if (next === seat || playedSeats.has(next) || teamOf(next) === teamOf(seat)) continue;
    const hand = game.hands[next] || [];
    const followers = hand.filter(candidate => effectiveSuit(candidate) === leadSuit);
    const choices = followers.length ? followers : hand;
    if (choices.some(candidate => beats(candidate, card, leadSuit))) return false;
  }
  return true;
}
function chooseFourteenCashout(seat, legal) {
  const lead = game.trick[0];
  if (!lead || lead.seat !== game.highBidder || seat === game.highBidder) return null;
  const leadSuit = effectiveSuit(lead.card);
  if (!leadSuit || cardRank(lead.card) >= 14 || cardAlreadyPlayed(leadSuit, 1)) return null;
  const suitCards = (game.hands[seat] || []).filter(card => effectiveSuit(card) === leadSuit);
  if (suitCards.length < 2) return null;
  return legal.find(card => !card.rook && card.value === 14 && effectiveSuit(card) === leadSuit) || null;
}
function bidderLedBelowHigh() {
  const lead = game.trick[0];
  return !!lead && lead.seat === game.highBidder && cardRank(lead.card) < 15;
}
function defendersCanTakeCurrentTrick(seat, winningCard, leadSuit) {
  if (teamOf(trickWinner(game.trick)) === 1) return true;
  if (legalCards(seat).some(card => beats(card, winningCard, leadSuit))) return true;
  const alreadyPlayed = new Set(game.trick.map(play => play.seat));
  return [0, 1, 2].some(other => {
    if (other === seat || alreadyPlayed.has(other) || teamOf(other) !== 1) return false;
    const hand = game.hands[other] || [];
    const followers = hand.filter(card => effectiveSuit(card) === leadSuit);
    const choices = followers.length ? followers : hand;
    return choices.some(card => beats(card, winningCard, leadSuit));
  });
}
function wouldStrand14(seat, card) {
  if (card.rook || card.value === 14 || cardAlreadyPlayed(card.suit, 1)) return false;
  const remain = game.hands[seat].filter(c => c.id !== card.id && !c.rook && c.suit === card.suit);
  return remain.length === 1 && remain[0].value === 14;
}
function isPointThrow(card) { return !!card && (card.rook || card.value === 10 || card.value === 5); }
function chooseSecondSeatBidderPointFeed(seat, legal) {
  if (game.trick.length !== 1 || game.trick[0].seat !== game.highBidder || game.trick[0].card.rook) return null;
  const leadCard = game.trick[0].card;
  const leadSuit = effectiveSuit(leadCard);
  const remainingInColor = game.hands.flat().filter(card => effectiveSuit(card) === leadSuit);
  const higherCards = remainingInColor.filter(card => cardRank(card) > cardRank(leadCard));
  if (!higherCards.length) return null;
  const highestRank = Math.max(...remainingInColor.map(cardRank));
  if ((game.hands[seat] || []).some(card => effectiveSuit(card) === leadSuit && cardRank(card) === highestRank)) return null;
  const points = legal.filter(isPointThrow);
  return points.sort((a, b) => cardPoints(b) - cardPoints(a) || cardRank(a) - cardRank(b))[0] || null;
}
function isEstablishedWinner(seat, card) {
  const leadSuit = effectiveSuit(card);
  return [0, 1, 2].filter(other => other !== seat && teamOf(other) !== teamOf(seat)).every(other => {
    const hand = game.hands[other] || [];
    const followers = hand.filter(candidate => effectiveSuit(candidate) === leadSuit);
    const responses = followers.length ? followers : hand;
    return !responses.some(candidate => beats(candidate, card, leadSuit));
  });
}
function botHasSideWinner(seat) {
  return (game.hands[seat] || []).some(card => effectiveSuit(card) !== game.trump && isEstablishedWinner(seat, card));
}
function bidderSecondarySuit() {
  const leads = game.playHistory.filter(play => play.seat === game.highBidder && play.led && effectiveSuit(play.card) !== game.trump);
  return leads.length ? effectiveSuit(leads[0].card) : null;
}
function protectSluffCards(seat, cards) {
  let pool = [...cards];
  const nonPoints = pool.filter(card => cardPoints(card) === 0);
  if (nonPoints.length) pool = nonPoints;
  const nonWinners = pool.filter(card => !(!card.rook && card.value === 1) && !isEstablishedWinner(seat, card));
  if (nonWinners.length) pool = nonWinners;
  const secondSuit = bidderSecondarySuit();
  if (seat !== game.highBidder && secondSuit && game.hands[seat].length > 3) {
    const alternatives = pool.filter(card => effectiveSuit(card) !== secondSuit);
    if (alternatives.length) pool = alternatives;
  }
  return pool;
}
function lowestSafe(cards, seat) {
  const pool = cards.length ? cards.slice() : [];
  const unstrand = pool.filter(c => !wouldStrand14(seat, c));
  const source = unstrand.length ? unstrand : pool;
  return source.sort((a, b) => {
    const keepA = a.rook ? 22 : a.value === 1 ? 100 : a.value === 14 ? 88 : a.value === 13 ? 34 : a.value === 12 ? 18 : 0;
    const keepB = b.rook ? 22 : b.value === 1 ? 100 : b.value === 14 ? 88 : b.value === 13 ? 34 : b.value === 12 ? 18 : 0;
    return keepA - keepB || cardPoints(a) - cardPoints(b) || cardRank(a) - cardRank(b);
  })[0];
}
function chooseBotCard(seat) {
  const rawLegal = legalCards(seat);
  const legal = legalCardsKeepingFinalTrump(seat, rawLegal);
  if (!legal.length) return null;
  const bidder = seat === game.highBidder;
  const lastToPlay = game.trick.length === 2;
  const currentWinner = game.trick.length ? trickWinner(game.trick) : null;
  const leadSuit = game.trick.length ? effectiveSuit(game.trick[0].card) : null;

  if (!game.trick.length) {
    let leads = legal.filter(c => !isGuarded14(c) && (!c.rook || (game.trump && game.trump !== 'none' && cardRank(c) >= 16)));
    const nonPointers = leads.filter(card => cardPoints(card) === 0);
    if (nonPointers.length) leads = leads.filter(card => !(!card.rook && card.value === 10));
    if (bidder && game.trump && game.trump !== 'none' && opponentsStillHoldTrump(seat)) {
      const trumps = leads.filter(c => effectiveSuit(c) === game.trump && (!c.rook || cardRank(c) >= 16));
      if (trumps.length) return trumps.sort((a, b) => cardRank(b) - cardRank(a))[0];
    }
    if (!bidder) {
      leads = leads.filter(c => !game.trump || effectiveSuit(c) !== game.trump);
      leads = leads.filter(c => {
        const suit = effectiveSuit(c);
        if (!suit || c.rook || c.value !== 1) return true;
        return ![0,1,2].some(op => op !== seat && !game.hands[op].some(x => effectiveSuit(x) === suit));
      });
      const bidderSideSuit = bidderSideSuitToAvoidAfterDefenderWin(seat);
      if (bidderSideSuit) {
        const differentNonTrump = legal.filter(c => effectiveSuit(c) !== bidderSideSuit && effectiveSuit(c) !== game.trump);
        const preferred = leads.filter(c => effectiveSuit(c) !== bidderSideSuit && effectiveSuit(c) !== game.trump);
        if (differentNonTrump.length) leads = preferred.length ? preferred : differentNonTrump;
      }
    }
    const established = leads.filter(card => isEstablishedWinner(seat, card));
    if (established.length) return established.sort((a, b) => cardRank(b) - cardRank(a))[0];
    const safe = leads.filter(c => cardPoints(c) === 0);
    if (safe.length) return lowestSafe(safe, seat);
    return lowestSafe(leads.length ? leads : legal, seat);
  }

  const winningPlay = game.trick.find(x => x.seat === currentWinner);
  const winningCards = legal.filter(c => beats(c, winningPlay.card, leadSuit));

  const fourteenCashout = chooseFourteenCashout(seat, legal);
  if (fourteenCashout) return fourteenCashout;

  const secondSeatPoints = chooseSecondSeatBidderPointFeed(seat, legal);
  if (secondSeatPoints) return secondSeatPoints;

  // When void, use trump to regain the lead before cashing established winners.
  if (teamOf(currentWinner) !== teamOf(seat) && botHasSideWinner(seat)) {
    const trumps = legal.filter(card => effectiveSuit(card) === game.trump && beats(card, winningPlay.card, leadSuit));
    if (trumps.length) return trumps.sort((a, b) => cardRank(a) - cardRank(b))[0];
  }

  // The two defenders are a side.  Do not steal a teammate's trick just to
  // win it again; feed 5s, 10s, and the Rook only when that trick is secure.
  if (teamOf(currentWinner) === teamOf(seat)) {
    const under = legal.filter(c => !beats(c, winningPlay.card, leadSuit));
    const pool = under.length ? under : legal;
    if (cardWinLooksSecure(seat, winningPlay.card, leadSuit)) {
      const points = legal.filter(card => isPointThrow(card)
        && (!beats(card, winningPlay.card, leadSuit) || cardWinLooksSecure(seat, card, leadSuit)));
      if (points.length) return points.sort((a, b) => cardPoints(b) - cardPoints(a) || cardRank(a) - cardRank(b))[0];
    }
    const safe = pool.filter(c => !isGuarded14(c) && !wouldStrand14(seat, c));
    const protectedPool = protectSluffCards(seat, safe.length ? safe : pool);
    return lowestSafe(protectedPool, seat);
  }

  if (lastToPlay && currentWinner !== seat && !bidder && teamOf(currentWinner) === 1) {
    const points = legal.filter(c => isPointThrow(c) && !beats(c, winningPlay.card, leadSuit));
    if (points.length) return points.sort((a, b) => cardPoints(b) - cardPoints(a) || cardRank(a) - cardRank(b))[0];
  }

  if (bidder && game.trump && game.trump !== 'none' && opponentsStillHoldTrump(seat)) {
    const trumps = legal.filter(c => effectiveSuit(c) === game.trump);
    if (trumps.length === 1 && legal.length > 1 && game.hands[seat].length <= 2) {
      const nonTrumps = legal.filter(c => effectiveSuit(c) !== game.trump);
      if (nonTrumps.length) return lowestSafe(nonTrumps, seat);
    }
  }

  if (winningCards.length) {
    const one = winningCards.find(c => !c.rook && c.value === 1);
    if (one) return one;
    return winningCards.sort((a, b) => cardRank(a) - cardRank(b))[0];
  }

  const safeSluffs = legal.filter(c => !isGuarded14(c) && !wouldStrand14(seat, c));
  return lowestSafe(protectSluffCards(seat, safeSluffs.length ? safeSluffs : legal), seat);
}

function bidderSideSuitToAvoidAfterDefenderWin(seat) {
  if (seat === game.highBidder || !game.lastTrick || game.lastTrick.winner !== seat) return null;
  const bidderLead = game.lastTrick.plays?.[0];
  if (!bidderLead || bidderLead.seat !== game.highBidder) return null;
  const suit = effectiveSuit(bidderLead.card);
  if (!suit || suit === game.trump) return null;
  return suit;
}

function legalCardsKeepingFinalTrump(seat, legal) {
  if (!game.trump || game.trump === 'none') return legal;
  const trumps = (game.hands[seat] || []).filter(card => effectiveSuit(card) === game.trump);
  if (trumps.length !== 1) return legal;
  const finalTrump = trumps[0];
  if (!legal.some(card => card.id === finalTrump.id)) return legal;
  const nonTrump = legal.filter(card => effectiveSuit(card) !== game.trump);
  if (!nonTrump.length) return legal;
  return mustSpendFinalTrumpToAvoidSet(seat, finalTrump, nonTrump) ? legal : nonTrump;
}

function mustSpendFinalTrumpToAvoidSet(seat, finalTrump, nonTrump) {
  if (seat !== game.highBidder || !game.trick.length || !game.highBid) return false;
  const currentWinner = trickWinner(game.trick);
  if (currentWinner === game.highBidder) return false;
  const leadSuit = effectiveSuit(game.trick[0].card);
  const winningPlay = game.trick.find(play => play.seat === currentWinner);
  if (!winningPlay || !beats(finalTrump, winningPlay.card, leadSuit)) return false;
  if (nonTrump.some(card => beats(card, winningPlay.card, leadSuit))) return false;
  if (game.highBid === 400) return true;
  const defenderPoints = [0, 1, 2]
    .filter(player => player !== game.highBidder)
    .reduce((sum, player) => sum + (game.handPoints[player] || 0), 0);
  const tablePoints = game.trick.reduce((sum, play) => sum + cardPoints(play.card), 0);
  const cheapestDiscard = Math.min(...nonTrump.map(card => cardPoints(card)));
  return defenderPoints + tablePoints + cheapestDiscard > 200 - game.highBid;
}

function beginGame() {
  if (game.started) return;
  ensureBots();
  game.started = true;
  game.scores = [0,0,0];
  game.botBidSetCounts = [0,0,0];
  game.botBidBlockedThroughHand = [0,0,0];
  game.handNumber = 0;
  game.dealer = Math.floor(Math.random() * 3);
  resetHand();
}
function botShouldVoteBitter(seat) {
  const hand = game.hands[seat] || [];
  const pointTotal = hand.reduce((total, card) => total + cardPoints(card), 0);
  if (!pointTotal) return true;
  const suits = SUITS.map(suit => hand.filter(card => !card.rook && card.suit === suit));
  const maxSuit = Math.max(...suits.map(cards => cards.length));
  const hasFourWithOne = suits.some(cards => cards.length >= 4 && cards.some(card => card.value === 1));
  const premium = hand.filter(card => card.rook || card.value === 1 || card.value === 14 || card.value === 13 || card.value === 12 || cardPoints(card) > 0).length;
  return maxSuit <= 3 || (!hasFourWithOne && premium <= 4);
}
function voteBitterBunch(seat) {
  if (game.phase !== 'bidding' || game.highBid || game.currentBidder !== seat || game.bitterVotes[seat]) return false;
  game.bitterVotes[seat] = true;
  if (game.bitterVotes.every(Boolean)) {
    game.prompt = 'Bitter Bunch agreed — redealing.';
    resetHand();
  } else {
    game.currentBidder = (seat + 1) % 3;
    game.prompt = `${playerName(game.currentBidder)} must bid or choose Bitter Bunch.`;
    scheduleBotBidIfNeeded();
  }
  return true;
}
function redealMisdeal(seat) {
  if (game.phase !== 'bidding' || game.highBid || !game.misdealSeats.includes(seat)) return false;
  game.prompt = `${playerName(seat)} has a misdeal — redealing.`;
  resetHand();
  return true;
}
function recordBid(seat, bid) {
  game.highBid = bid;
  game.bitterVotes = [false, false, false];
  game.highBidder = seat;
  game.lastBidderName = playerName(seat);
  game.bidHistory.push({ seat, bid, passed: false });
}
function passBid(seat) {
  game.passed[seat] = true;
  game.bidHistory.push({ seat, bid: 'Pass', passed: true });
}
function advanceBidding() {
  const active = [0,1,2].filter(i => !game.passed[i]);
  if (game.highBidder !== null && active.length === 1 && active[0] === game.highBidder) return finishBidding();
  if (!active.length) {
    game.highBid = 0; game.highBidder = null; game.passed = [false,false,false]; game.bidHistory = [];
    game.currentBidder = (game.dealer + 1) % 3;
  } else {
    let next = null;
    for (let step = 1; step <= 3; step++) {
      const candidate = (game.currentBidder + step) % 3;
      if (!game.passed[candidate]) { next = candidate; break; }
    }
    game.currentBidder = next;
  }
  game.prompt = `${playerName(game.currentBidder)} to bid.`;
  scheduleBotBidIfNeeded();
}
function runBotBidding() {
  if (!game.started || game.phase !== 'bidding' || game.currentBidder === null || !game.bot[game.currentBidder]) return;
  const seat = game.currentBidder;
  if (botBidIsSuspended(game.currentBidder)) {
    if (!game.highBid) {
      voteBitterBunch(seat);
      return;
    }
    passBid(seat);
    game.prompt = `${playerName(seat)} must pass after being set twice.`;
    advanceBidding();
    return;
  }
  const next = minLegalBid();
  if (!game.highBid) {
    if (botShouldVoteBitter(seat)) {
      voteBitterBunch(seat);
      return;
    }
    recordBid(seat, BID_START);
  } else {
    const maxBid = estimateMaxBid(game.hands[seat]);
    if (next <= 400 && next <= maxBid) recordBid(seat, next); else passBid(seat);
  }
  advanceBidding();
}

function botBidIsSuspended(seat) {
  return game.handNumber <= (game.botBidBlockedThroughHand[seat] || 0);
}

function recordBotBidResult(seat, madeBid, bidderPoints = 0) {
  if (seat === null || !game.bot[seat] || madeBid) return;
  const deficit = Math.max(0, game.highBid - (Number(bidderPoints) || 0));
  const strikes = deficit > 40 ? 2 : 1;
  game.botBidSetCounts[seat] = (game.botBidSetCounts[seat] || 0) + strikes;
  if (game.botBidSetCounts[seat] < 2) return;
  game.botBidSetCounts[seat] = 0;
  game.botBidBlockedThroughHand[seat] = game.handNumber + 3;
}
function scheduleBotBidIfNeeded() {
  clearTimeout(botTimer);
  if (game.phase === 'bidding' && game.currentBidder !== null && game.bot[game.currentBidder]) botTimer = setTimeout(runBotBidding, BOT_DELAY.bid);
}

function finishBidding() {
  game.phase = 'pickup';
  game.bidTeam = game.highBidder;
  game.kittyAccepted = false;
  game.selectedDiscards = [];
  sortHand(game.hands[game.highBidder]);
  game.prompt = `${playerName(game.highBidder)} won the bid at ${game.highBid}. View the kitty, accept it, then choose trump.`;
  if (game.bot[game.highBidder]) botFinishPickup();
}
function acceptKitty(seat) {
  if (game.phase !== 'pickup' || game.highBidder !== seat || game.kittyAccepted) return false;
  game.hands[seat].push(...game.kitty);
  game.kitty = [];
  game.kittyAccepted = true;
  sortHand(game.hands[seat]);
  game.prompt = `${playerName(seat)} accepted the kitty. Choose trump.`;
  return true;
}
function chooseTrump(seat, trump) {
  if (game.phase !== 'pickup' || game.highBidder !== seat || !game.kittyAccepted) return false;
  if (!(SUITS.includes(trump) || trump === 'none')) return false;
  game.trump = trump;
  game.phase = 'discard';
  game.hands.forEach(sortHand);
  game.prompt = `${playerName(seat)} chose ${trump === 'none' ? 'No Trump' : `${trump} trump`}. Return 9 cards to the kitty.`;
  return true;
}

function changeTrump(seat) {
  if (game.highBidder !== seat || !game.kittyAccepted || game.trick.length || game.playedCards.length) return false;
  if (game.phase === 'playing') {
    game.hands[seat].push(...game.kitty);
    game.kitty = [];
  } else if (game.phase !== 'discard') return false;
  game.trump = null;
  game.selectedDiscards = [];
  game.phase = 'pickup';
  game.hands.forEach(sortHand);
  game.prompt = `${playerName(seat)} may choose a different trump before returning the kitty.`;
  return true;
}
function changeKitty(seat) {
  if (game.phase !== 'playing' || game.highBidder !== seat || game.trick.length || game.playedCards.length) return false;
  game.hands[seat].push(...game.kitty);
  game.kitty = [];
  game.selectedDiscards = [];
  game.phase = 'discard';
  sortHand(game.hands[seat]);
  game.prompt = `${playerName(seat)} may choose a different 9-card kitty before leading.`;
  return true;
}
function selectDiscards(seat, ids) {
  if (game.phase !== 'discard' || game.highBidder !== seat || !Array.isArray(ids)) return false;
  const unique = [...new Set(ids)].filter(id => game.hands[seat].some(c => c.id === id));
  if (unique.length > KITTY_SIZE) return false;
  game.selectedDiscards = unique;
  return true;
}
function finishDiscard(seat) {
  if (game.phase !== 'discard' || game.highBidder !== seat || game.selectedDiscards.length !== KITTY_SIZE) return false;
  const ids = new Set(game.selectedDiscards);
  game.kitty = game.hands[seat].filter(c => ids.has(c.id));
  game.hands[seat] = game.hands[seat].filter(c => !ids.has(c.id));
  game.selectedDiscards = [];
  sortHand(game.hands[seat]);
  game.leader = seat; game.turn = seat; game.trick = []; game.phase = 'playing'; game.prompt = `${playerName(seat)} leads.`;
  scheduleTurn();
  return true;
}
function botFinishPickup() {
  const seat = game.highBidder;
  if (!game.bot[seat] || game.phase !== 'pickup') return;
  acceptKitty(seat);
  const trump = chooseBestTrump(game.hands[seat]);
  chooseTrump(seat, trump);
  clearTimeout(botTimer);
  botTimer = setTimeout(() => {
    if (!game.bot[seat] || game.phase !== 'discard' || game.highBidder !== seat || game.trump !== trump) return;
    const discards = chooseBotDiscards(game.hands[seat], trump);
    selectDiscards(seat, discards.map(c => c.id));
    finishDiscard(seat);
  }, TRUMP_REVEAL_MS);
}
function resolveTrick() {
  const winner = trickWinner(game.trick);
  const points = game.trick.reduce((n, x) => n + cardPoints(x.card), 0);
  game.handPoints[winner] += points;
  game.tricksWon[winner] += 1;
  game.lastTrick = { plays: game.trick.map(x => ({ seat: x.seat, card: { ...x.card } })), winner, points };
  game.revealUntil = now() + TRICK_REVEAL_MS;
  game.phase = 'trickReveal';
  game.prompt = `${playerName(winner)} won the trick.`;
  clearTimeout(revealTimer);
  revealTimer = setTimeout(() => {
    game.trick = [];
    if (game.hands.every(h => h.length === 0)) scoreHand();
    else { game.leader = winner; game.turn = winner; game.phase = 'playing'; game.prompt = `${playerName(winner)} leads.`; scheduleTurn(); }
  }, TRICK_REVEAL_MS);
}
function scheduleTurn() {
  clearTimeout(botTimer);
  if (game.phase === 'playing' && game.bot[game.turn]) botTimer = setTimeout(() => botPlay(game.turn), BOT_DELAY.play);
}
function playCard(seat, cardId) {
  if (game.phase !== 'playing' || game.turn !== seat) return false;
  const legal = new Set(legalCards(seat).map(c => c.id));
  if (!legal.has(cardId)) return false;
  const index = game.hands[seat].findIndex(c => c.id === cardId);
  if (index < 0) return false;
  const card = game.hands[seat].splice(index, 1)[0];
  game.playedCards.push({ ...card });
  game.playHistory.push({ seat, card: { ...card }, led: game.trick.length === 0 });
  game.trick.push({ seat, card });
  if (game.trick.length === 3) resolveTrick();
  else { game.turn = (seat + 1) % 3; game.prompt = `${playerName(game.turn)} to play.`; scheduleTurn(); }
  return true;
}
function botPlay(seat) {
  if (game.phase !== 'playing' || game.turn !== seat || !game.bot[seat]) return;
  if (canClaimRest(seat)) { claimRest(seat); return; }
  const card = chooseBotCard(seat);
  if (card) playCard(seat, card.id);
}
function canClaimRest(seat) {
  if (game.phase !== 'playing' || game.highBidder !== seat || game.turn !== seat || game.trick.length || !(game.hands[seat] || []).length) return false;
  const bidderHand = game.hands[seat].map(card => ({ ...card }));
  const opponentHands = [0, 1, 2].filter(i => i !== seat).map(i => game.hands[i].map(card => ({ ...card })));
  const remove = (hand, card) => { const index = hand.findIndex(item => item.id === card.id); if (index >= 0) hand.splice(index, 1); };
  while (bidderHand.length) {
    const lead = [...bidderHand].sort((a, b) => cardRank(b) - cardRank(a) || cardPoints(b) - cardPoints(a))[0];
    const leadSuit = effectiveSuit(lead);
    for (const hand of opponentHands) {
      const followers = hand.filter(card => effectiveSuit(card) === leadSuit);
      const legal = followers.length ? followers : hand;
      if (legal.some(card => beats(card, lead, leadSuit))) return false;
      if (followers.length) remove(hand, [...followers].sort((a, b) => cardRank(a) - cardRank(b) || cardPoints(a) - cardPoints(b))[0]);
    }
    remove(bidderHand, lead);
  }
  return true;
}
function claimRest(seat) {
  if (!canClaimRest(seat)) return false;
  clearTimeout(botTimer); clearTimeout(revealTimer);
  game.claimReveal = game.hands.map(hand => hand.map(card => ({ ...card })));
  const remaining = game.hands.flatMap(hand => hand.splice(0));
  const points = remaining.reduce((total, card) => total + cardPoints(card), 0);
  game.handPoints[seat] += points;
  game.tricksWon[seat] += remaining.length / 3;
  game.lastTrick = { plays: [], winner: seat, points };
  game.trick = [];
  game.prompt = `${playerName(seat)} claims the remaining tricks.`;
  scoreHand();
  return true;
}
function canGoDown(seat) {
  if (!['pickup', 'discard', 'playing', 'trickReveal'].includes(game.phase) || game.highBidder !== seat) return false;
  const facedLiveOpponent = game.humanSeatsThisHand.some((isHuman, player) => isHuman && player !== seat);
  if (!facedLiveOpponent) return true;
  const bidderCardsPlayed = game.playHistory.filter(play => play.seat === seat).length;
  return bidderCardsPlayed < 6;
}
function goDown(seat) {
  if (!canGoDown(seat)) return false;
  clearTimeout(botTimer); clearTimeout(revealTimer);
  const bidder = game.highBidder;
  const defenders = [0, 1, 2].filter(player => player !== bidder);
  game.claimReveal = game.hands.map(hand => hand.map(card => ({ ...card })));
  game.hands = [[], [], []];
  game.trick = [];
  game.selectedDiscards = [];
  game.handPoints = [0, 0, 0];
  game.scores[bidder] = Math.max(0, game.scores[bidder] - game.highBid);
  recordBotBidResult(bidder, false, 0);
  game.lastHandResult = {
    bid: game.highBid,
    bidder,
    bidderPoints: 0,
    bidMade: false,
    defenderTotal: 0,
    defenderShares: defenders.map(player => ({ seat: player, name: playerName(player), points: 0 })),
    totalPoints: 0,
    wentDown: true
  };
  game.phase = 'scoring';
  game.prompt = `${playerName(bidder)} went down and loses the ${game.highBid} bid.`;
  const winner = game.scores.findIndex(score => score >= WIN_SCORE);
  if (winner >= 0) { game.winner = winner; game.phase = 'gameover'; }
  return true;
}

function scoreHand() {
  const lastWinner = game.lastTrick?.winner ?? game.leader;
  const kittyPoints = game.kitty.reduce((n, c) => n + cardPoints(c), 0) + 20;
  const points = game.handPoints.slice();
  points[lastWinner] += kittyPoints;
  const bidder = game.highBidder;
  const defenders = [0,1,2].filter(seat => seat !== bidder);
  const bidderPoints = points[bidder] || 0;
  const defenderTotal = defenders.reduce((n, seat) => n + (points[seat] || 0), 0);
  const madeBid = bidderPoints >= game.highBid;
  recordBotBidResult(bidder, madeBid, bidderPoints);
  const defenderShares = [
    { seat: defenders[0], name: playerName(defenders[0]), points: defenderTotal },
    { seat: defenders[1], name: playerName(defenders[1]), points: defenderTotal },
  ];
  game.scores[bidder] = madeBid ? game.scores[bidder] + bidderPoints : Math.max(0, game.scores[bidder] - game.highBid);
  game.scores[defenders[0]] += defenderTotal;
  game.scores[defenders[1]] += defenderTotal;
  game.lastHandResult = {
    bid: game.highBid,
    bidder,
    bidderPoints,
    bidMade: madeBid,
    defenderTotal,
    defenderShares,
    totalPoints: bidderPoints + defenderTotal
  };
  game.phase = 'scoring';
  game.prompt = `Hand ${game.handNumber} complete.`;
  const winner = game.scores.findIndex(s => s >= WIN_SCORE);
  if (winner >= 0) { game.winner = winner; game.phase = 'gameover'; }
}

function publicState(seat) {
  const hand = seat >= 0 ? game.hands[seat] || [] : [];
  const visibleKitty = seat === game.highBidder ? game.kitty : [];
  return {
    version: VERSION,
    phase: game.phase,
    handNumber: game.handNumber,
    dealer: game.dealer,
    currentBidder: game.currentBidder,
    highBid: game.highBid,
    highBidder: game.highBidder,
    lastBidderName: game.lastBidderName,
    bidHistory: game.bidHistory,
    passed: game.passed,
    prompt: game.prompt,
    trump: game.trump,
    kitty: visibleKitty,
    kittyCount: game.kitty.length,
    kittyAccepted: game.kittyAccepted,
    cardsPlayed: game.playedCards.length,
    selectedDiscards: seat === game.highBidder ? game.selectedDiscards : [],
    hands: [0,1,2].map(i => i === seat ? (game.hands[i] || []) : []),
    handCounts: game.hands.map(h => h.length),
    trick: game.trick,
    lastTrick: game.lastTrick,
    revealUntil: game.revealUntil,
    turn: game.turn,
    leader: game.leader,
    scores: game.scores,
    handPoints: game.handPoints,
    tricksWon: game.tricksWon,
    lastHandResult: game.lastHandResult,
    defenders: game.highBidder === null ? [] : [0,1,2].filter(i => i !== game.highBidder),
    seats: PLAYER_NAMES.map((name, i) => ({ seat: i, name, connected: game.live[i], bot: game.bot[i] })),
    chat: game.chat,
    winner: game.winner,
    canClaimRest: canClaimRest(seat),
    canGoDown: canGoDown(seat),
    claimReveal: game.claimReveal,
    bitterVotes: game.bitterVotes,
    canRedeal: game.phase === 'bidding' && !game.highBid && game.misdealSeats.includes(seat),
  };
}
function getSession(token) { return sessions.get(String(token || '')) || null; }
function refreshLive() {
  const cutoff = now() - PLAYER_TIMEOUT_MS;
  for (let i = 0; i < 3; i++) {
    if (game.live[i] && game.lastSeen[i] < cutoff) {
      game.live[i] = false;
      if (game.started) game.bot[i] = true;
    }
  }
}
function json(res, status, payload) {
  const body = JSON.stringify(payload);
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store', 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'Content-Type' });
  res.end(body);
  return true;
}
function readJson(req) {
  return new Promise((resolve, reject) => {
    let body = '';
    req.on('data', chunk => { body += chunk; if (body.length > 10000) req.destroy(); });
    req.on('end', () => { try { resolve(body ? JSON.parse(body) : {}); } catch (e) { reject(e); } });
    req.on('error', reject);
  });
}
async function api(req, res) {
  refreshLive();
  if (req.method === 'OPTIONS') { res.writeHead(204, { 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'Content-Type' }); res.end(); return true; }
  if (req.method === 'POST' && req.url === '/api/join') {
    const data = await readJson(req);
    const name = cleanName(data.name);
    if (!name) return json(res, 400, { ok: false, message: 'Choose Daryl, Cristi, or Cindy.' });
    let seat = PLAYER_NAMES.indexOf(name);
    const current = sessions.get(data.token || '');
    if (current && current.name === name) seat = current.seat;
    game.live[seat] = true; game.bot[seat] = false; game.lastSeen[seat] = now(); game.humanSeatsThisHand[seat] = true;
    const token = current?.token || makeId('s_');
    sessions.set(token, { token, name, seat });
    if (game.started && game.bot[seat]) game.bot[seat] = false;
    return json(res, 200, { ok: true, token, name, seat, state: publicState(seat) });
  }
  if (req.method === 'GET' && req.url.startsWith('/api/state')) {
    const url = new URL(req.url, `http://${req.headers.host || 'localhost'}`);
    const session = getSession(url.searchParams.get('token'));
    if (!session) return json(res, 401, { ok: false, message: 'Session expired. Choose your player again.' });
    game.live[session.seat] = true; game.bot[session.seat] = false; game.lastSeen[session.seat] = now();
    return json(res, 200, { ok: true, state: publicState(session.seat) });
  }
  if (req.method === 'POST' && req.url === '/api/heartbeat') {
    const data = await readJson(req); const s = getSession(data.token);
    if (!s) return json(res, 401, { ok: false, message: 'Session expired.' });
    game.live[s.seat] = true; game.bot[s.seat] = false; game.lastSeen[s.seat] = now();
    return json(res, 200, { ok: true });
  }
  if (req.method === 'POST' && req.url === '/api/action') {
    const data = await readJson(req); const s = getSession(data.token);
    if (!s) return json(res, 401, { ok: false, message: 'Session expired.' });
    game.live[s.seat] = true; game.bot[s.seat] = false; game.lastSeen[s.seat] = now();
    let ok = true;
    if (data.action === 'start') beginGame();
    else if (data.action === 'bitterBunch') ok = voteBitterBunch(s.seat);
    else if (data.action === 'redeal') ok = redealMisdeal(s.seat);
    else if (data.action === 'bid') {
      if (game.phase !== 'bidding' || game.currentBidder !== s.seat || game.bot[s.seat]) ok = false;
      else { const bid = Number(data.bid); const min = minLegalBid(); if (!Number.isFinite(bid) || bid < min || bid > 400 || (bid > 200 && bid < 400)) ok = false; else { recordBid(s.seat, bid); advanceBidding(); } }
    } else if (data.action === 'pass') {
      if (game.phase !== 'bidding' || !game.highBid || game.currentBidder !== s.seat || game.bot[s.seat]) ok = false; else { passBid(s.seat); advanceBidding(); }
    } else if (data.action === 'acceptKitty') ok = acceptKitty(s.seat);
    else if (data.action === 'trump') ok = chooseTrump(s.seat, data.trump);
    else if (data.action === 'changeTrump') ok = changeTrump(s.seat);
    else if (data.action === 'changeKitty') ok = changeKitty(s.seat);
    else if (data.action === 'selectDiscard' || data.action === 'selectDiscards') ok = selectDiscards(s.seat, data.cardIds);
    else if (data.action === 'discard') { ok = selectDiscards(s.seat, data.cardIds); if (ok) ok = finishDiscard(s.seat); }
    else if (data.action === 'play') ok = playCard(s.seat, data.cardId);
    else if (data.action === 'claimRest') ok = claimRest(s.seat);
    else if (data.action === 'goDown') ok = goDown(s.seat);
    else if (data.action === 'chat') { const text = String(data.text || '').trim().slice(0, 240); if (text) game.chat.push({ name: playerName(s.seat), text, at: now() }); game.chat = game.chat.slice(-60); }
    else if (data.action === 'nextHand') { if (game.phase === 'scoring') resetHand(); else ok = false; }
    else if (data.action === 'newGame') { game.scores = [0,0,0]; game.botBidSetCounts = [0,0,0]; game.botBidBlockedThroughHand = [0,0,0]; game.handNumber = 0; game.started = false; game.winner = null; resetHand(); game.started = true; }
    else ok = false;
    if (game.phase === 'bidding') scheduleBotBidIfNeeded();
    if (!ok) return json(res, 400, { ok: false, message: 'That action is not available right now.', state: publicState(s.seat) });
    return json(res, 200, { ok: true, state: publicState(s.seat) });
  }
  return false;
}

const server = http.createServer(async (req, res) => {
  try {
    const handled = await api(req, res);
    if (handled) return;
    const requestPath = req.url === '/' ? '/index.html' : req.url.split('?')[0];
    const relative = path.normalize(requestPath).replace(/^[/\\]+/, '');
    const filePath = path.join(PUBLIC_DIR, relative);
    if (!filePath.startsWith(PUBLIC_DIR)) { res.writeHead(403); res.end('Forbidden'); return; }
    fs.readFile(filePath, (err, content) => {
      if (err) { res.writeHead(err.code === 'ENOENT' ? 404 : 500); res.end(err.code === 'ENOENT' ? 'Not found' : 'Server error'); return; }
      const ext = path.extname(filePath).toLowerCase();
      const type = ext === '.html' ? 'text/html; charset=utf-8' : ext === '.js' ? 'application/javascript; charset=utf-8' : 'application/octet-stream';
      res.writeHead(200, { 'Content-Type': type, 'Cache-Control': 'no-store' }); res.end(content);
    });
  } catch (error) { console.error(error); json(res, 500, { ok: false, message: 'Server error.' }); }
});

server.listen(PORT, HOST, () => console.log(`3-Handed Judd Rook ${VERSION} listening on ${HOST}:${PORT}`));
