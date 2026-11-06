'use strict';
/*
 * MONOPOLY: NAPOLI — онлайн-сервер (Node.js + Express + Socket.IO).
 *
 * Принцип работы: сервер — единственный источник истины. Он загружает ИГРОВОЙ КОД из public/index.html
 * (скрипты с атрибутом data-engine — это ваши оригинальные правила: бросок, покупка, аренда, карты,
 * аукцион, залог, дома/отели, тюрьма, банкротство) и выполняет его в изолированном vm-контексте
 * для каждой комнаты. Клиенты присылают только НАМЕРЕНИЯ ("бросить", "купить", "ставка +10"),
 * сервер проверяет, что действие делает тот, чья очередь, и рассылает всем итоговое состояние.
 * Клиент не может прислать состояние партии.
 */
const fs = require('fs');
const path = require('path');
const http = require('http');
const vm = require('vm');
const crypto = require('crypto');
const express = require('express');
const { Server } = require('socket.io');

/* ===================== НАСТРОЙКИ (переменные окружения) ===================== */
const PORT = Number(process.env.PORT) || 3000;
/* Игра и сервер работают на одном адресе (Render), поэтому CORS не нужен. CORS_ORIGINS — необязательный список
   дополнительных сайтов (через запятую), если когда-нибудь понадобится открывать игру с другого домена. */
const FRONTEND_ORIGINS = (process.env.CORS_ORIGINS || '').split(',').map(s => s.trim()).filter(Boolean);
const MAX_PLAYERS = 8;
const MIN_PLAYERS = 2;
const num = (v, d) => { const n = Number(v); return Number.isFinite(n) && n >= 0 ? n : d; };
const AUTO_AFTER_MS = num(process.env.AUTOPLAY_AFTER_MS, 45000);   // через сколько отключённый игрок начинает «ходить автоматически»
const AUTO_STEP_MS = num(process.env.AUTOPLAY_STEP_MS, 1200);      // пауза между автоматическими шагами
const ABSENT_LIMIT_MS = num(process.env.ABSENT_LIMIT_MS, 10 * 60 * 1000); // через сколько отключённый игрок окончательно исключается из партии
const LOBBY_GRACE_MS = num(process.env.LOBBY_GRACE_MS, 60 * 1000); // сколько держим место отключённого игрока в лобби
const ROOM_IDLE_MS = num(process.env.ROOM_IDLE_MS, 30 * 60 * 1000); // комната без подключённых игроков живёт столько
const MAX_ROOMS = Math.max(1, Math.floor(num(process.env.MAX_ROOMS, 200)));
const PUBLIC_DIR = path.join(__dirname, 'public');
const HTML_PATH = path.join(PUBLIC_DIR, 'index.html');

/* ===================== ДВИЖОК: ваш игровой код в vm ===================== */
const ENGINE_PATCH = `
var __out={toasts:[],fx:[]};
toast=function(t){__out.toasts.push(String(t))};
AU.fx=function(k){__out.fx.push(String(k))};
AU.init=function(){};AU.startM=function(){};AU.stopM=function(){};AU.vol=function(){};
render=function(){if(S)ens()};
save=function(){};
Date.prototype.toLocaleTimeString=function(){return ''};
var __API=(function(){
 const I=(v,lo,hi)=>Number.isInteger(v)&&v>=lo&&v<=hi;
 const actor=()=>S.debt?S.debt.f:S.cur;
 const own=(seat,i)=>I(i,0,39)&&isP(C[i])&&S.b[i].o===seat;
 function snap(){if(!S)return null;const s=Object.assign({},S,{dk:{ch:S.dk.ch.map(()=>0),cc:S.dk.cc.map(()=>0)}});return JSON.stringify(s)}
 function needed(){if(!S||S.ph=='win')return[];
  if(S.tr)return S.tr.st==1?[S.tr.a,S.tr.b]:[S.tr.a];
  if(S.ph=='auc'&&S.au&&S.au.act.length)return[S.au.act[S.au.t]];
  return[actor()]}
 function tradeAct(seat,type,a,T,act){
  if(type=='trade_open'){
   if(T)return 'Сделка уже открыта';if(seat!==act)return 'Сейчас не ваш ход';
   if(['roll','act','debt'].indexOf(S.ph)<0)return 'Сейчас нельзя торговаться';
   if(S.p.filter(x=>!x.out).length<2)return 'Не с кем торговаться';
   openT();return S.tr?'':'Не удалось открыть сделку'}
  if(!T)return 'Сделка не открыта';
  if(type=='trade_cancel'){if(seat!==T.a&&seat!==T.b)return 'Это не ваша сделка';S.tr=null;return ''}
  if(type=='trade_accept'){if(seat!==T.b||T.st!==1)return 'Принять сделку может только её адресат';acc();return ''}
  if(seat!==T.a)return 'Сделку редактирует её автор';
  if(type=='trade_edit'){if(T.st!==1)return 'Сделка не предложена';T.st=0;return ''}
  if(T.st!==0)return 'Сначала нажмите «Изменить»';
  if(type=='trade_propose'){T.st=1;return ''}
  if(type=='trade_partner'){const b=a[0];if(!I(b,0,S.p.length-1)||b===T.a||S.p[b].out)return 'Неверный партнёр';T.b=b;T.pb=[];return ''}
  if(type=='trade_toggle'){const k=a[0],i=a[1];if(k!=='pa'&&k!=='pb')return 'Неверный список';if(!I(i,0,39))return 'Неверная клетка';
   const o=k=='pa'?T.a:T.b;if(!tp(o).some(c=>c.i===i))return 'Этот объект нельзя включить в сделку';tg(k,i);return ''}
  if(type=='trade_cash'){const k=a[0],v=a[1];if(k!=='ca'&&k!=='cb')return 'Неверное поле';if(typeof v!=='number'||!isFinite(v))return 'Неверная сумма';t_(v,k);return ''}
  return 'Неизвестное действие'}
 function run(inp){
  const seat=inp.seat,type=String(inp.type),a=Array.isArray(inp.a)?inp.a:[];
  if(!S)return{err:'Партия не начата'};
  if(S.ph=='win')return{err:'Партия окончена'};
  const P=S.p[seat];if(!P||P.out)return{err:'Вы выбыли из партии'};
  const before=snap();__out.toasts.length=0;__out.fx.length=0;FQ.length=0;DR=0;
  const T=S.tr,act=actor();let err='';
  if(type.indexOf('trade_')==0)err=tradeAct(seat,type,a,T,act);
  else{
   const bidder=S.ph=='auc'&&S.au?S.au.act[S.au.t]:-1;
   switch(type){
    case 'roll':if(S.ph!='roll'||seat!==act)err='Сейчас нельзя бросать кубики';break;
    case 'pj':case 'uj':if(S.ph!='roll'||seat!==act)err='Сейчас нельзя';break;
    case 'end':if(S.ph!='act'||seat!==act)err='Сейчас нельзя завершить ход';break;
    case 'buy':case 'dc':if(S.ph!='buy'||seat!==S.cur)err='Сейчас нельзя покупать';else if(S.b[S.p[seat].pos].o!==-1)err='Объект уже куплен';break;
    case 'ap':if(S.ph!='card'||seat!==S.cur)err='Сейчас нельзя';break;
    case 'pd':case 'bk':if(S.ph!='debt'||!S.debt||seat!==S.debt.f)err='У вас нет долга';break;
    case 'bid':{const k=a[0];if(S.ph!='auc'||seat!==bidder)err='Сейчас торгуется другой игрок';else if(k!==1&&k!==10&&k!==50&&k!==100)err='Неверная ставка';break}
    case 'ps':if(S.ph!='auc'||seat!==bidder)err='Сейчас торгуется другой игрок';break;
    case 'bd':case 'sl':case 'mg':case 'um':{const i=a[0];
     if(['roll','act','debt'].indexOf(S.ph)<0||seat!==act)err='Сейчас нельзя управлять имуществом';
     else if(!own(seat,i))err='Это не ваша собственность';
     else if((type=='bd'||type=='sl')&&C[i].t!='p')err='Здания строятся только на улицах';
     else if(type=='um'&&!S.b[i].z)err='Объект не в залоге';
     else if(type=='mg'&&S.b[i].z)err='Объект уже в залоге';
     break}
    default:err='Неизвестное действие'}
   if(!err){
    if(S.tr)S.tr=null;
    const i=a[0];
    switch(type){case 'roll':roll();break;case 'pj':pj();break;case 'uj':uj();break;case 'end':end();break;case 'buy':buy();break;case 'dc':dc();break;
     case 'ap':ap();break;case 'pd':pd();break;case 'bk':bk();break;case 'bid':bid(a[0]);break;case 'ps':ps();break;
     case 'bd':bd(i);break;case 'sl':sl(i);break;case 'mg':mg(i);break;case 'um':um(i);break}}}
  if(S)ens();
  const after=snap();
  return{err:err,changed:before!==after,json:after,fx:__out.fx.slice(),toasts:__out.toasts.slice(),fq:FQ.splice(0),roll:DR?1:0,ph:S.ph}}
 function forfeit(seat){
  if(!S||S.ph=='win')return{err:'Партия окончена'};
  const p=S.p[seat];if(!p||p.out)return{err:'Игрок уже выбыл'};
  const before=snap();__out.toasts.length=0;__out.fx.length=0;FQ.length=0;DR=0;
  const pos0=p.pos;
  L(p.n+' покинул партию. Имущество уходит на аукцион');
  if(S.tr&&(S.tr.a==seat||S.tr.b==seat))S.tr=null;
  C.forEach(c=>{const b=S.b[c.i];if(!isP(c)||b.o!=seat||!b.h)return;if(b.h==5)S.hotels++;else S.houses+=b.h;b.h=0});
  if(p.m>0)tr(seat,-1,p.m,'остаток средств игрока, покинувшего партию');
  p.jf.forEach(k=>S.dk[k].push(FI[k]));
  if(S.ph=='card'&&S.cd&&S.cur==seat){S.dk[S.cd.k].push(S.cd.id);S.cd=null}
  if(S.ph=='buy'&&S.cur==seat&&isP(C[pos0])&&S.b[pos0].o==-1)S.aq.unshift(pos0);
  C.forEach(c=>{const b=S.b[c.i];if(!isP(c)||b.o!=seat)return;b.o=-1;b.z=0;if(S.aq.indexOf(c.i)<0)S.aq.push(c.i)});
  p.m=0;p.jf=[];p.out=1;p.pos=-1;
  S.eq=S.eq.filter(e=>e.f!=seat&&e.t!=seat);
  ens();if(S.bo.indexOf(seat)<0)S.bo.push(seat);
  AU.fx('bad');
  if(S.p.filter(x=>!x.out).length<2){S.ph='win';S.au=null;S.debt=null;S.cd=null;S.tr=null}
  else if(S.ph=='auc'&&S.au){
   const a=S.au,k=a.act.indexOf(seat);
   if(k>=0){a.act.splice(k,1);if(k<a.t)a.t--}
   if(a.lead==seat){a.lead=-1;a.bid=0}
   if(a.t>=a.act.length)a.t=0;
   chk()}
  else if(S.ph=='debt'){
   if(S.debt&&(S.debt.f==seat||S.debt.t==seat)){S.debt=null;pump()}}
  else if(S.cur==seat){S.pm=0;S.cd=null;S.debt=null;fin()}
  if(S)ens();
  const after=snap();
  return{err:'',changed:before!==after,json:after,fx:__out.fx.slice(),toasts:__out.toasts.slice(),fq:FQ.splice(0),roll:0,ph:S.ph}}
 function autoStep(seat){
  if(!S||S.ph=='win')return{err:'Партия окончена'};
  if(S.tr&&(S.tr.a==seat||S.tr.b==seat))return run({seat:seat,type:'trade_cancel',a:[]});
  switch(S.ph){
   case 'roll':return run({seat:seat,type:'roll',a:[]});
   case 'act':return run({seat:seat,type:'end',a:[]});
   case 'buy':return run({seat:seat,type:'dc',a:[]});
   case 'card':return run({seat:seat,type:'ap',a:[]});
   case 'auc':return run({seat:seat,type:'ps',a:[]});
   case 'debt':{
    const d=S.debt;if(!d||d.f!==seat)return{err:'Не ваш долг'};
    const before=snap();__out.toasts.length=0;__out.fx.length=0;FQ.length=0;DR=0;
    let g=0;
    while(S.p[d.f].m<d.a&&g++<300){let did=0;
     for(const c of C){if(c.t=='p'&&S.b[c.i].o==d.f&&S.b[c.i].h>0&&canS(c)){sl(c.i);did=1;break}}
     if(!did)for(const c of C){if(isP(c)&&S.b[c.i].o==d.f&&!S.b[c.i].z&&canM(c)){mg(c.i);did=1;break}}
     if(!did)break}
    if(S.ph=='debt'&&S.debt&&S.p[d.f].m>=d.a)pd();else if(S.ph=='debt'&&S.debt)bk();
    if(S)ens();
    const after=snap();
    return{err:'',changed:before!==after,json:after,fx:__out.fx.slice(),toasts:__out.toasts.slice(),fq:FQ.splice(0),roll:0,ph:S.ph}}
   default:return{err:'Нечего делать'}}}
 function start(cfg){
  SU.n=cfg.players.length;SU.mode=cfg.mode?1:0;SU.rounds=cfg.rounds;SU.cf=0;SU.err='';
  SU.pl=cfg.players.map(x=>({n:x.n,t:x.t,c:x.c,bot:0}));
  __out.toasts.length=0;__out.fx.length=0;FQ.length=0;
  st();if(!S)return{err:'Не удалось начать партию'};
  ens();return{err:'',changed:true,json:snap(),fx:[],toasts:[],fq:[],roll:0,ph:S.ph}}
 return{run:run,forfeit:forfeit,autoStep:autoStep,start:start,needed:needed,snap:snap}
})();
`;

function extractEngineSources(html) {
  const re = /<script\s+data-engine[^>]*>([\s\S]*?)<\/script>/g;
  const out = [];
  let m;
  while ((m = re.exec(html))) out.push(m[1]);
  if (out.length < 2) throw new Error('В public/index.html не найдены скрипты с атрибутом data-engine (игровой код).');
  return out;
}

let ENGINE_SCRIPTS = null;
function loadEngineScripts() {
  const html = fs.readFileSync(HTML_PATH, 'utf8');
  ENGINE_SCRIPTS = extractEngineSources(html).map((s, i) => new vm.Script(s, { filename: 'game-engine-' + i + '.js' }))
    .concat([new vm.Script(ENGINE_PATCH, { filename: 'engine-patch.js' })]);
}

/* Заглушки браузерного окружения: ваш код правил обращается к DOM только при отрисовке, на сервере она отключена. */
function makeSandbox() {
  const mkEl = () => ({
    style: { setProperty() {} }, classList: { toggle() {}, add() {}, remove() {} }, setAttribute() {}, getAttribute() { return null },
    appendChild() {}, addEventListener() {}, querySelector() { return null }, querySelectorAll() { return []; }, innerHTML: '', textContent: ''
  });
  const nullStore = { getItem: () => null, setItem() {}, removeItem() {} };
  const sb = {
    console: { log() {}, error() {}, warn() {} }, setTimeout: () => 0, clearTimeout() {}, setInterval: () => 0, clearInterval() {},
    addEventListener() {}, innerWidth: 1280, innerHeight: 800, screen: { width: 1280, height: 800 }, devicePixelRatio: 1,
    navigator: {}, matchMedia: () => ({ matches: false }), localStorage: nullStore, sessionStorage: nullStore
  };
  sb.window = sb;
  sb.document = { getElementById: mkEl, querySelector: mkEl, querySelectorAll: () => [], addEventListener() {}, createElement: mkEl, documentElement: mkEl(), body: mkEl(), fonts: null, hidden: false };
  sb.Element = function Element() {};
  sb.Element.prototype.animate = function () {};
  return sb;
}

class Engine {
  constructor() {
    if (!ENGINE_SCRIPTS) loadEngineScripts();
    this.ctx = vm.createContext(makeSandbox());
    for (const s of ENGINE_SCRIPTS) s.runInContext(this.ctx, { timeout: 5000 });
  }
  call(expr, input) {
    this.ctx.__inJson = JSON.stringify(input === undefined ? null : input);
    const raw = vm.runInContext('JSON.stringify(' + expr + '(JSON.parse(__inJson)))', this.ctx, { timeout: 3000 });
    return raw === undefined ? null : JSON.parse(raw);
  }
  start(cfg) { return this.call('__API.start', cfg); }
  run(seat, type, args) { return this.call('__API.run', { seat, type, a: args }); }
  forfeit(seat) { return this.call('__API.forfeit', seat); }
  autoStep(seat) { return this.call('__API.autoStep', seat); }
  needed() { return this.call('__API.needed', null) || []; }
  meta() { return this.call('(function(){return{PC:PC,TK:TK}})', null); }
}

/* ===================== КОМНАТЫ ===================== */
const rooms = new Map();
const sockets = new Map(); // socket.id -> socket
let META = null;
const CODE_ALPHABET = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789';

function genCode() {
  for (let n = 0; n < 200; n++) {
    let c = '';
    for (let i = 0; i < 5; i++) c += CODE_ALPHABET[crypto.randomInt(CODE_ALPHABET.length)];
    if (!rooms.has(c)) return c;
  }
  throw new Error('Не удалось создать код комнаты');
}
const cleanName = (s) => String(s == null ? '' : s).replace(/[\u0000-\u001f\u007f<>&"'`]/g, '').replace(/\s+/g, ' ').trim().slice(0, 14);
function uniqueName(room, name, exceptId) {
  const base = cleanName(name) || 'Игрок';
  let n = base, k = 2;
  const taken = (x) => room.players.some(p => p.id !== exceptId && p.name.toLowerCase() === x.toLowerCase());
  while (taken(n)) { n = (base.slice(0, 11) + ' ' + k++).trim(); }
  return n;
}
const freeIndex = (room, key, max, except) => {
  for (let i = 0; i < max; i++) if (!room.players.some(p => p.id !== except && p[key] === i)) return i;
  return 0;
};

function newRoom(hostName) {
  const room = {
    code: genCode(), host: null, players: [], started: false, finished: false, mode: 0, rounds: 30,
    engine: null, json: null, seq: 0, created: Date.now(), touched: Date.now(), autoTimer: null
  };
  rooms.set(room.code, room);
  return room;
}
function addPlayer(room, name) {
  const p = {
    id: crypto.randomBytes(5).toString('hex'), token: crypto.randomBytes(18).toString('hex'),
    name: uniqueName(room, name), ti: freeIndex(room, 'ti', MAX_PLAYERS), ci: freeIndex(room, 'ci', MAX_PLAYERS),
    ready: false, connected: true, socketId: null, discAt: 0, left: false, timer: null
  };
  room.players.push(p);
  return p;
}
const seatOf = (room, p) => room.players.indexOf(p);

function publicRoom(room, me) {
  return {
    code: room.code, started: room.started, finished: room.finished, mode: room.mode, rounds: room.rounds, max: MAX_PLAYERS,
    host: room.host, you: me ? me.id : null, seat: me ? seatOf(room, me) : -1,
    players: room.players.map((p, i) => ({
      id: p.id, seat: i, name: p.name, t: p.ti, c: META.PC[p.ci], ci: p.ci, ready: p.id === room.host ? true : p.ready,
      connected: p.connected, left: p.left, host: p.id === room.host
    }))
  };
}
function sendTo(p, event, payload) {
  const s = p.socketId && sockets.get(p.socketId);
  if (s) { try { s.emit(event, payload); } catch (e) { /* соединение закрыто */ } }
}
function broadcastRoom(room) {
  room.touched = Date.now();
  for (const p of room.players) if (p.connected) sendTo(p, 'room', publicRoom(room, p));
}
function ensureHost(room) {
  const cur = room.players.find(p => p.id === room.host);
  if (cur && cur.connected && !cur.left) return;
  const nh = room.players.find(p => p.connected && !p.left);
  if (nh) room.host = nh.id; else if (!cur || cur.left) { const any = room.players.find(p => !p.left); room.host = any ? any.id : null; }
}
function destroyRoom(room) {
  if (room.autoTimer) clearTimeout(room.autoTimer);
  room.players.forEach(p => { if (p.timer) clearTimeout(p.timer); });
  rooms.delete(room.code);
}

/* Рассылка нового состояния всем игрокам комнаты */
function publish(room, res) {
  room.json = res.json;
  room.seq++;
  room.touched = Date.now();
  if (res.ph === 'win') room.finished = true;
  const payload = { seq: room.seq, state: res.json, fx: res.fx || [], toasts: res.toasts || [], fq: res.fq || [], roll: res.roll ? 1 : 0 };
  for (const p of room.players) if (p.connected) sendTo(p, 'state', payload);
  if (room.finished) broadcastRoom(room);
  checkAuto(room);
}

/* Если тот, чьего действия ждёт партия, отключён — через AUTO_AFTER_MS сервер ходит за него простыми безопасными шагами */
function checkAuto(room) {
  if (room.autoTimer) { clearTimeout(room.autoTimer); room.autoTimer = null; }
  if (!room.started || room.finished || !room.engine) return;
  let need;
  try { need = room.engine.needed(); } catch (e) { return; }
  const off = need.find(s => { const p = room.players[s]; return p && !p.left && !p.connected; });
  if (off === undefined) return;
  const p = room.players[off];
  const delay = Math.max(AUTO_STEP_MS, (p.discAt || Date.now()) + AUTO_AFTER_MS - Date.now());
  room.autoTimer = setTimeout(() => {
    room.autoTimer = null;
    if (!rooms.has(room.code) || room.finished) return;
    const pl = room.players[off];
    if (!pl || pl.connected || pl.left) { checkAuto(room); return; }
    try {
      if (room.engine.needed().indexOf(off) >= 0) {
        const res = room.engine.autoStep(off);
        if (!res.err && res.changed) { publish(room, res); return; }
        if (res.err || !res.changed) { const f = room.engine.forfeit(off); if (!f.err && f.changed) { pl.left = true; publish(room, f); broadcastRoom(room); return; } }
      }
    } catch (e) { console.error('autoplay error', e); }
    checkAuto(room);
  }, delay);
}

/* Окончательный выход игрока из партии (по кнопке или по таймеру отсутствия) */
function removeFromGame(room, p) {
  if (p.left) return;
  const seat = seatOf(room, p);
  if (room.started && !room.finished) {
    try {
      const res = room.engine.forfeit(seat);
      if (!res.err && res.changed) { p.left = true; p.connected = false; publish(room, res); }
    } catch (e) { console.error('forfeit error', e); }
  }
  p.left = true; p.connected = false;
  if (p.timer) { clearTimeout(p.timer); p.timer = null; }
  ensureHost(room);
  broadcastRoom(room);
  maybeCleanup(room);
}
function removeFromLobby(room, p) {
  if (p.timer) { clearTimeout(p.timer); p.timer = null; }
  room.players = room.players.filter(x => x !== p);
  ensureHost(room);
  if (!room.players.length) { destroyRoom(room); return; }
  broadcastRoom(room);
}
function maybeCleanup(room) {
  if (!room.players.some(p => !p.left)) destroyRoom(room);
}

function onDisconnect(room, p) {
  p.connected = false; p.socketId = null; p.discAt = Date.now();
  if (p.timer) clearTimeout(p.timer);
  if (!room.started) {
    p.timer = setTimeout(() => { p.timer = null; if (rooms.has(room.code) && !p.connected && !room.started) removeFromLobby(room, p); }, LOBBY_GRACE_MS);
  } else if (!room.finished) {
    p.timer = setTimeout(() => { p.timer = null; if (rooms.has(room.code) && !p.connected) removeFromGame(room, p); }, ABSENT_LIMIT_MS);
  }
  ensureHost(room);
  broadcastRoom(room);
  checkAuto(room);
}

/* ===================== HTTP + SOCKET.IO ===================== */
const app = express();
app.disable('x-powered-by');
app.use((req, res, next) => {
  const o = req.headers.origin;
  if (o && FRONTEND_ORIGINS.indexOf(o) >= 0) { res.setHeader('Access-Control-Allow-Origin', o); res.setHeader('Vary', 'Origin'); }
  next();
});
app.get('/health', (req, res) => {
  res.status(200).json({ status: 'ok', uptime: Math.round(process.uptime()), rooms: rooms.size, time: new Date().toISOString() });
});
app.use(express.static(PUBLIC_DIR, { index: 'index.html', maxAge: '1h' }));
app.get('/', (req, res) => res.sendFile(HTML_PATH));

const server = http.createServer(app);
const io = new Server(server, {
  ...(FRONTEND_ORIGINS.length ? { cors: { origin: FRONTEND_ORIGINS, methods: ['GET', 'POST'] } } : {}),
  transports: ['websocket', 'polling'],
  pingInterval: 20000, pingTimeout: 25000, maxHttpBufferSize: 1e5
});

io.on('connection', (socket) => {
  sockets.set(socket.id, socket);
  const bind = { room: null, pid: null };
  let bucket = 0, bucketAt = Date.now();
  const limited = () => {
    const now = Date.now();
    if (now - bucketAt > 10000) { bucket = 0; bucketAt = now; }
    return ++bucket > 80;
  };
  const me = () => {
    const room = bind.room && rooms.get(bind.room);
    if (!room) return {};
    const p = room.players.find(x => x.id === bind.pid && x.socketId === socket.id);
    return p ? { room, p } : {};
  };
  const handler = (fn) => (payload, cb) => {
    const reply = typeof cb === 'function' ? cb : () => {};
    try {
      if (limited()) return reply({ ok: false, error: 'Слишком много запросов. Подождите секунду.' });
      fn(payload && typeof payload === 'object' ? payload : {}, reply);
    } catch (e) {
      console.error('handler error', e);
      reply({ ok: false, error: 'Внутренняя ошибка сервера' });
    }
  };
  const attach = (room, p) => {
    if (p.socketId && p.socketId !== socket.id) {
      const old = sockets.get(p.socketId);
      if (old) { try { old.emit('kicked', { reason: 'Вы подключились с другого устройства или вкладки' }); } catch (e) { /* ignore */ } }
    }
    p.socketId = socket.id; p.connected = true; p.discAt = 0;
    if (p.timer) { clearTimeout(p.timer); p.timer = null; }
    bind.room = room.code; bind.pid = p.id;
    try { socket.join(room.code); } catch (e) { /* ignore */ }
  };

  socket.on('room:create', handler((d, reply) => {
    if (bind.room) return reply({ ok: false, error: 'Вы уже в комнате' });
    if (rooms.size >= MAX_ROOMS) return reply({ ok: false, error: 'Сервер перегружен, попробуйте позже' });
    const room = newRoom();
    const p = addPlayer(room, d.name);
    room.host = p.id;
    attach(room, p);
    reply({ ok: true, code: room.code, token: p.token, id: p.id });
    broadcastRoom(room);
  }));

  socket.on('room:join', handler((d, reply) => {
    if (bind.room) return reply({ ok: false, error: 'Вы уже в комнате' });
    const code = String(d.code || '').toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 8);
    const room = rooms.get(code);
    if (!room) return reply({ ok: false, error: 'Комната не найдена' });
    if (room.started) return reply({ ok: false, error: 'Партия уже началась. Вернуться можно только со своего устройства.' });
    if (room.players.length >= MAX_PLAYERS) return reply({ ok: false, error: 'Комната заполнена (максимум 8 игроков)' });
    const p = addPlayer(room, d.name);
    attach(room, p);
    reply({ ok: true, code: room.code, token: p.token, id: p.id });
    broadcastRoom(room);
  }));

  socket.on('room:rejoin', handler((d, reply) => {
    const code = String(d.code || '').toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 8);
    const room = rooms.get(code);
    const token = typeof d.token === 'string' ? d.token : '';
    const p = room && token ? room.players.find(x => x.token === token) : null;
    if (!room || !p || p.left) return reply({ ok: false, error: 'Комната или место в партии не найдены', gone: true });
    attach(room, p);
    ensureHost(room);
    reply({ ok: true, code: room.code, token: p.token, id: p.id });
    broadcastRoom(room);
    if (room.started && room.json) sendTo(p, 'state', { seq: room.seq, state: room.json, fx: [], toasts: [], fq: [], roll: 0, resync: true });
    checkAuto(room);
  }));

  socket.on('room:leave', handler((d, reply) => {
    const { room, p } = me();
    if (!room) return reply({ ok: true });
    bind.room = null; bind.pid = null;
    try { socket.leave(room.code); } catch (e) { /* ignore */ }
    p.socketId = null; p.connected = false;
    if (!room.started) removeFromLobby(room, p); else removeFromGame(room, p);
    reply({ ok: true });
  }));

  socket.on('room:ready', handler((d, reply) => {
    const { room, p } = me();
    if (!room || room.started) return reply({ ok: false, error: 'Недоступно' });
    p.ready = !!d.ready;
    reply({ ok: true });
    broadcastRoom(room);
  }));

  socket.on('room:profile', handler((d, reply) => {
    const { room, p } = me();
    if (!room || room.started) return reply({ ok: false, error: 'Менять профиль можно только до начала партии' });
    if (d.name !== undefined) p.name = uniqueName(room, d.name, p.id);
    if (d.t !== undefined) {
      const t = d.t;
      if (!Number.isInteger(t) || t < 0 || t >= MAX_PLAYERS || room.players.some(x => x !== p && x.ti === t)) return reply({ ok: false, error: 'Эта фишка занята' });
      p.ti = t;
    }
    if (d.ci !== undefined) {
      const c = d.ci;
      if (!Number.isInteger(c) || c < 0 || c >= MAX_PLAYERS || room.players.some(x => x !== p && x.ci === c)) return reply({ ok: false, error: 'Этот цвет занят' });
      p.ci = c;
    }
    reply({ ok: true });
    broadcastRoom(room);
  }));

  socket.on('room:settings', handler((d, reply) => {
    const { room, p } = me();
    if (!room || room.started) return reply({ ok: false, error: 'Недоступно' });
    if (room.host !== p.id) return reply({ ok: false, error: 'Настройки меняет только создатель комнаты' });
    if (d.mode !== undefined) room.mode = d.mode ? 1 : 0;
    if (d.rounds !== undefined) { const r = Math.floor(Number(d.rounds)); room.rounds = Number.isFinite(r) ? Math.max(3, Math.min(200, r)) : 30; }
    reply({ ok: true });
    broadcastRoom(room);
  }));

  socket.on('room:start', handler((d, reply) => {
    const { room, p } = me();
    if (!room) return reply({ ok: false, error: 'Вы не в комнате' });
    if (room.started) return reply({ ok: false, error: 'Партия уже идёт' });
    if (room.host !== p.id) return reply({ ok: false, error: 'Начать игру может только создатель комнаты' });
    const pl = room.players.filter(x => !x.left);
    if (pl.length < MIN_PLAYERS) return reply({ ok: false, error: 'Нужно минимум 2 игрока' });
    if (pl.some(x => !x.connected)) return reply({ ok: false, error: 'Кто-то из игроков отключился — подождите или дождитесь его возвращения' });
    if (pl.some(x => x.id !== room.host && !x.ready)) return reply({ ok: false, error: 'Не все игроки готовы' });
    const engine = new Engine();
    const res = engine.start({ players: room.players.map(x => ({ n: x.name, t: x.ti, c: META.PC[x.ci] })), mode: room.mode, rounds: room.rounds });
    if (res.err) return reply({ ok: false, error: res.err });
    room.engine = engine; room.started = true;
    reply({ ok: true });
    broadcastRoom(room);
    publish(room, res);
  }));

  socket.on('game:act', handler((d, reply) => {
    const { room, p } = me();
    if (!room || !room.started || !room.engine) return reply({ ok: false, error: 'Партия не идёт' });
    if (room.finished) return reply({ ok: false, error: 'Партия окончена' });
    if (typeof d.type !== 'string' || d.type.length > 24 || !/^[a-z_]+$/.test(d.type)) return reply({ ok: false, error: 'Неверное действие' });
    const args = Array.isArray(d.args) ? d.args.slice(0, 4).filter(x => typeof x === 'number' || typeof x === 'string') : [];
    const res = room.engine.run(seatOf(room, p), d.type, args);
    if (res.err) return reply({ ok: false, error: res.err });
    if (!res.changed) return reply({ ok: false, error: 'Действие сейчас недоступно' });
    reply({ ok: true });
    publish(room, res);
  }));

  socket.on('disconnect', () => {
    sockets.delete(socket.id);
    const room = bind.room && rooms.get(bind.room);
    if (!room) return;
    const p = room.players.find(x => x.id === bind.pid);
    if (p && p.socketId === socket.id) onDisconnect(room, p);
  });
});

/* Уборка заброшенных комнат */
const sweeper = setInterval(() => {
  const now = Date.now();
  for (const room of Array.from(rooms.values())) {
    const anyone = room.players.some(p => p.connected);
    if (!anyone && now - room.touched > ROOM_IDLE_MS) destroyRoom(room);
  }
}, 60 * 1000);
if (sweeper.unref) sweeper.unref();

function start() {
  loadEngineScripts();
  const probe = new Engine();
  META = probe.meta();
  if (!META || !Array.isArray(META.PC) || META.PC.length < MAX_PLAYERS) throw new Error('Не удалось прочитать палитру игры из index.html');
  if (!fs.existsSync(path.join(PUBLIC_DIR, 'three.min.js'))) console.warn('ВНИМАНИЕ: public/three.min.js не найден — 3D возьмётся из резервного CDN или не включится. Выполните npm install (файл копируется автоматически).');
  server.listen(PORT, '0.0.0.0', () => console.log('Monopoly Napoli server listening on port ' + PORT + (FRONTEND_ORIGINS.length ? '; extra CORS origins: ' + FRONTEND_ORIGINS.join(', ') : '')));
}

process.on('unhandledRejection', (e) => console.error('unhandledRejection', e));
process.on('uncaughtException', (e) => console.error('uncaughtException', e));
process.on('SIGTERM', () => { console.log('SIGTERM'); try { io.close(); } catch (e) { /* ignore */ } server.close(() => process.exit(0)); setTimeout(() => process.exit(0), 3000).unref(); });

if (require.main === module) start();
module.exports = { Engine, loadEngineScripts, io, rooms, start };
