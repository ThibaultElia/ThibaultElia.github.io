// Moteur partagé : écoute au micro, notes qui tombent, boutons. Chaque page fournit sa partition.

window.PianoTrainer=function(def){
'use strict';

/* ================= Musique ================= */
const NOTE_FR=['Do','Do♯','Ré','Ré♯','Mi','Fa','Fa♯','Sol','Sol♯','La','La♯','Si'];
const NOTE_EN=['C','C♯','D','D♯','E','F','F♯','G','G♯','A','A♯','B'];
const pc=m=>((Math.round(m)%12)+12)%12;
const nameFr=m=>NOTE_FR[pc(m)];
const nameEn=m=>NOTE_EN[pc(m)];
const isBlack=m=>[1,3,6,8,10].includes(pc(m));

function N(beat,dur,m){return {beat,dur,m:Array.isArray(m)?m:[m]};}
const eighths=(start,arr)=>arr.map((m,i)=>N(start+i*.5,.5,m));
const rep=(n,v)=>Array(n).fill(v);
const SONG=def({N,eighths,rep});
const PARTS=SONG.parts,ORDER=SONG.order,SECTION_IDS=[...ORDER,'tout'];
const BPM=SONG.bpm,BAR=SONG.bar||4; // BAR = temps par mesure (le temps est l'unité de la partition)

/* ================= Réglages mémorisés ================= */
const KEY=SONG.key;
let saved={};try{saved=JSON.parse(localStorage.getItem(KEY)||'{}')||{};}catch(e){saved={};}
function save(){try{localStorage.setItem(KEY,JSON.stringify(saved));}catch(e){}}
saved.stars=saved.stars||{};

/* ================= État ================= */
const S={
  sec:SECTION_IDS.includes(saved.sec)?saved.sec:SONG.start,
  hand:['lh','both'].includes(saved.hand)?saved.hand:'rh',
  bassOnly:saved.bassOnly===true, loop:0, loopA:0, loopB:0, loops:0,
  mode:saved.mode==='rhythm'?'rhythm':'wait',
  speed:typeof saved.speed==='number'?Math.min(1.2,Math.max(.3,saved.speed)):.5,
  sens:typeof saved.sens==='number'?saved.sens:6,
  phase:'idle', clock:-2, notes:[], pending:0, last:-1, mic:false, manual:false,
  lo:57, hi:76, keyFx:{}
};
const bps=()=>BPM/60*S.speed;
const effHand=()=>PARTS[S.sec].rh.length?S.hand:'lh';
const offOf=()=>PARTS[S.sec].off||0; // temps où commence la mesure 1 (après une éventuelle anacrouse)
// Les notes à jouer : une main, ou les deux regroupées par moment (tout ce qui commence au même temps).
function sectionNotes(){
  const p=PARTS[S.sec],h=effHand(),lhOk=n=>!S.bassOnly||(SONG.isBass?SONG.isBass(n,PARTS[S.sec]):n.m.length===1);
  let src;
  if(h==='both'){
    const all=[...p.rh.filter(n=>(n.hand||'rh')==='rh').map(n=>({...n,hand:'rh'})),...p.lh.filter(lhOk).map(n=>({...n,hand:'lh'}))];
    const by=new Map();
    all.forEach(n=>{const k=n.beat.toFixed(3);if(!by.has(k))by.set(k,{beat:n.beat,parts:[]});by.get(k).parts.push({m:n.m,dur:n.dur,hand:n.hand});});
    src=[...by.values()].sort((a,b)=>a.beat-b.beat);
  }else{
    src=p[h].filter(n=>(n.hand||h)==='rh'||lhOk(n)).map(n=>({beat:n.beat,parts:[{m:n.m,dur:n.dur,hand:n.hand||h}]}));
  }
  return src.map((g,i)=>{const hands=new Set(g.parts.map(q=>q.hand));
    return {beat:g.beat,dur:Math.max(...g.parts.map(q=>q.dur)),m:[...new Set(g.parts.flatMap(q=>q.m))],parts:g.parts,
      hand:hands.size>1?'both':[...hands][0],rh:g.parts.filter(q=>q.hand==='rh').flatMap(q=>q.m),
      lh:g.parts.filter(q=>q.hand==='lh').flatMap(q=>q.m),i,st:'todo',slip:false};});
}

function loadSection(){
  S.notes=sectionNotes();S.loop=0;S.loops=0;
  S.pending=0;S.last=-1;S.clock=S.mode==='rhythm'?-4:-2;S.phase='idle';
  S.endBeat=Math.max(...S.notes.map(n=>n.beat+n.dur))+.5;
  S.hits=0;S.perfect=0;S.errors=0;S.keyFx={};S.seeked=false;S.countEnd=0;
  // clavier : juste les touches utiles, au moins deux octaves
  let lo=Math.min(...S.notes.flatMap(n=>n.m))-1,hi=Math.max(...S.notes.flatMap(n=>n.m))+1;
  while(countWhite(lo,hi)<15){lo--;if(countWhite(lo,hi)<15)hi++;}
  while(isBlack(lo))lo--;while(isBlack(hi))hi++;
  S.lo=lo;S.hi=hi;
  demoStop();hideEnd();setBig('');
  updateNoteCards(true);renderChips();renderPlay();
}
function countWhite(a,b){let c=0;for(let m=a;m<=b;m++)if(!isBlack(m))c++;return c;}

/* ================= Audio ================= */
let ctx=null,master=null,an=null,an2=null,tbuf=null,fbuf=null,cbuf=null,prevMag=null;
function ensureCtx(){
  if(!ctx){const AC=window.AudioContext||window.webkitAudioContext;ctx=new AC();master=ctx.createGain();master.gain.value=.8;master.connect(ctx.destination);}
  if(ctx.state==='suspended')ctx.resume();
  return ctx;
}
async function startMic(){
  ensureCtx();
  if(!navigator.mediaDevices||!navigator.mediaDevices.getUserMedia)throw new Error('nomedia');
  const stream=await navigator.mediaDevices.getUserMedia({audio:{echoCancellation:false,noiseSuppression:false,autoGainControl:false}});
  const src=ctx.createMediaStreamSource(stream);
  an=ctx.createAnalyser();an.fftSize=2048;an.smoothingTimeConstant=0;src.connect(an);
  an2=ctx.createAnalyser();an2.fftSize=8192;an2.smoothingTimeConstant=0;src.connect(an2);cbuf=new Float32Array(an2.frequencyBinCount);
  tbuf=new Float32Array(an.fftSize);fbuf=new Float32Array(an.frequencyBinCount);prevMag=new Float32Array(an.frequencyBinCount);
  S.mic=true;
}

// Son de piano synthétique (partiels qui s'éteignent), pour « Écouter ».
const pianoCache={};
function pianoBuf(m){
  if(pianoCache[m])return pianoCache[m];
  const sr=ctx.sampleRate,f0=440*Math.pow(2,(m-69)/12),dur=m<55?3:2.2,n=Math.floor(sr*dur);
  const buf=ctx.createBuffer(1,n,sr),d=buf.getChannelData(0);
  for(let h=1;h<=10;h++){
    const f=h*f0*Math.sqrt(1+.0004*h*h);if(f>sr/2.3)break;
    const amp=Math.pow(h,-1.15)*(h===2?.8:1),k=(1.1+.55*h)*Math.pow(f0/262,.35);
    const w=2*Math.PI*f/sr,c=2*Math.cos(w);let y1=Math.sin(-w),y2=Math.sin(-2*w),e=amp;const de=Math.exp(-k/sr);
    for(let i=0;i<n;i++){const y=c*y1-y2;y2=y1;y1=y;d[i]+=y*e;e*=de;}
  }
  let peak=0;for(let i=0;i<n;i++){const a=Math.min(1,i/(sr*.004));d[i]*=a;peak=Math.max(peak,Math.abs(d[i]));}
  const g=peak?.85/peak:1;for(let i=0;i<n;i++)d[i]*=g;
  return pianoCache[m]=buf;
}
const voices=new Set();
function strike(m,when,len,vol){
  const s=ctx.createBufferSource();s.buffer=pianoBuf(m);
  const g=ctx.createGain();g.gain.setValueAtTime(vol,when);g.gain.setTargetAtTime(0,when+Math.max(.1,len),.08);
  s.connect(g);g.connect(master);s.start(when);s.stop(when+len+.8);
  voices.add(s);s.onended=()=>voices.delete(s);
}
function click(when,strong){
  const o=ctx.createOscillator(),g=ctx.createGain();o.frequency.value=strong?1760:1320;
  g.gain.setValueAtTime(.0001,when);g.gain.exponentialRampToValueAtTime(.35,when+.002);g.gain.exponentialRampToValueAtTime(.0001,when+.05);
  o.connect(g);g.connect(master);o.start(when);o.stop(when+.06);
}

/* ================= Écoute (hauteur + attaque) ================= */
const DET={rms:0,floor:.002,flux:0,flh:[],env:[],sh:[],lastOnset:-1e9,pitch:null,hist:[],attempt:null,stable:[],mute:0};
let ds=null,cm=null,dd=null;
function yin(x,sr){
  const Nn=x.length,tauMax=Math.min(Math.floor(sr/72),Nn>>1),tauMin=Math.max(2,Math.floor(sr/1500)),W=Nn-tauMax;
  if(!dd||dd.length<tauMax+2){dd=new Float32Array(tauMax+2);cm=new Float32Array(tauMax+2);}
  for(let t=1;t<=tauMax;t++){let s=0;for(let i=0;i<W;i++){const v=x[i]-x[i+t];s+=v*v;}dd[t]=s;}
  let run=0;cm[0]=1;for(let t=1;t<=tauMax;t++){run+=dd[t];cm[t]=run>0?dd[t]*t/run:1;}
  let tau=-1;
  for(let t=tauMin;t<=tauMax;t++){if(cm[t]<.15){while(t+1<=tauMax&&cm[t+1]<cm[t])t++;tau=t;break;}}
  if(tau<0){let mi=tauMin;for(let t=tauMin;t<=tauMax;t++)if(cm[t]<cm[mi])mi=t;if(cm[mi]<.3)tau=mi;else return null;}
  const a=cm[tau-1],b=cm[tau],c=tau+1<=tauMax?cm[tau+1]:b,den=a+c-2*b,sh=den?(a-c)/(2*den):0;
  return {f:sr/(tau+sh),conf:1-b};
}
const toMidi=f=>69+12*Math.log2(f/440);
function gate(){return Math.max(.0025,DET.floor*(11-S.sens)*.9+.0015);}

function analyse(ts){
  if(!an)return;
  an.getFloatTimeDomainData(tbuf);
  let s=0;for(let i=tbuf.length-512;i<tbuf.length;i++)s+=tbuf[i]*tbuf[i];
  const rms=Math.sqrt(s/512);DET.rms=rms;
  if(rms<DET.floor)DET.floor=DET.floor*.7+rms*.3;else if(rms<DET.floor*3)DET.floor=Math.min(.05,DET.floor*1.002);
  DET.floor=Math.max(DET.floor,.0003);
  an.getFloatFrequencyData(fbuf);let fl=0;
  const hi=Math.min(fbuf.length-1,400);
  for(let i=8;i<hi;i++){const mag=Math.pow(10,fbuf[i]/20);const df=mag-prevMag[i];if(df>0)fl+=df;prevMag[i]=mag;}
  DET.flux=fl;
  DET.sh.push({t:ts,d:Float32Array.from(fbuf)});while(DET.sh.length>12)DET.sh.shift();
  // flux de référence = médiane des images récentes (un battement entre cordes ne le fait pas bondir, un coup de marteau oui)
  const flMed=DET.flh.length?[...DET.flh].sort((a,b)=>a-b)[DET.flh.length>>1]:fl;DET.flh.push(fl);if(DET.flh.length>8)DET.flh.shift();
  const q=fl/Math.max(flMed,1e-5);
  const g=gate();let pitch=null;
  if(rms>g){
    if(!ds||ds.length!==tbuf.length>>1)ds=new Float32Array(tbuf.length>>1);
    for(let i=0;i<ds.length;i++)ds[i]=(tbuf[2*i]+tbuf[2*i+1])*.5;
    const r=yin(ds,ctx.sampleRate/2);
    if(r&&r.conf>.82&&r.f>70&&r.f<1500)pitch=toMidi(r.f);
  }
  DET.pitch=pitch;
  const pre=DET.hist.length?[...DET.hist].sort((a,b)=>a-b)[DET.hist.length>>1]:null; // ce qui sonnait juste avant
  if(pitch!==null){DET.hist.push(pitch);if(DET.hist.length>3)DET.hist.shift();}else DET.hist.length=0;
  // attaque (on ne remonte pas avant la dernière attaque, pour ne pas la redéclencher pendant sa montée)
  DET.env.push({t:ts,v:rms});while(DET.env.length&&DET.env[0].t<ts-110)DET.env.shift();
  let mn=1;for(let i=0;i<DET.env.length-1;i++)if(DET.env[i].t>DET.lastOnset)mn=Math.min(mn,DET.env[i].v);
  if(mn===1)mn=rms;
  let onset=false;const strong=q>=4||rms>mn*4; // coup de marteau, ou volume qui bondit (un battement ne fait jamais ×4)
  if(ts-DET.lastOnset>85&&rms>g*1.4&&ts>DET.mute){
    if(rms>mn*1.45+.0015)onset=true;
    else if(strong&&q>=6&&rms>mn*1.1)onset=true;
  }
  if(onset){const prevOn=DET.lastOnset;DET.lastOnset=ts;
    // une attaque faible (battement) n'écrase jamais une attaque franche encore en cours d'analyse
    if(strong||!DET.attempt||DET.attempt.weak){const a={t:ts,clock:S.clock-bps()*.03,samples:[],weak:!strong,pre,mn};
      const tg=attemptTarget(a);if(melodyCheck(tg)&&specRead()){a.base=tg.rh.map(trio);a.lhBase=tg.lh.map(m=>lhParts(m,tg.rh));
        // creux juste avant l'attaque, sans remonter avant l'attaque précédente
        a.sbase=tg.rh.map(m=>{let v=Infinity;for(const e of DET.sh)if(e.t>=Math.max(ts-110,prevOn+15)&&e.t<ts-8)v=Math.min(v,shortMag(m,e.d));
          if(v===Infinity){const e=DET.sh[DET.sh.length-2];v=e?shortMag(m,e.d):0;}return v;});}
      DET.attempt=a;}}
  const at=DET.attempt;
  // une attaque jugée faible à sa toute première image peut se confirmer franche dans les 50 ms qui suivent
  if(at&&at.weak&&ts-at.t<=50&&(q>=4||rms>at.mn*4))at.weak=false;
  if(at){
    const tgt=attemptTarget(at),chord=!!(tgt&&tgt.m.length>1);
    if(pitch!==null&&ts-at.t>20)at.samples.push(pitch);
    const sm=at.samples,L=sm.length,avg=L>=2?(sm[L-1]+sm[L-2])/2:0;
    const stable=L>=2&&Math.abs(sm[L-1]-sm[L-2])<.6;
    if(melodyCheck(tgt)){
      // Deux mains : la main gauche couvre le grave, on vérifie la mélodie (main droite) :
      // soit on l'entend seule, soit sa note vient de ressortir nettement plus que ses voisines.
      const age=ts-at.t,yinOK=stable&&tgt.rh.some(x=>Math.abs(x-avg)<=.6);
      if(at.weak){if(age>200)DET.attempt=null;} // battement de ce qui sonne déjà : ignoré
      else if(age>=60&&(yinOK||melodyHeard(tgt,at.base,at.sbase,age))&&leftHeard(tgt,at.lhBase)){DET.attempt=null;resolveAttempt(at,tgt.rh[0],ts);}
      else if(age>340)DET.attempt=null;
    }
    else if(chord){
      // Accord : une attaque faible (battement de ce qui sonne déjà) ne compte pas. Une attaque franche compte
      // si la hauteur entendue tombe dans l'accord, ou si aucune hauteur unique ne ressort (plusieurs notes à la fois).
      if(at.weak){if(ts-at.t>200)DET.attempt=null;}
      else if(stable){DET.attempt=null;const lo=Math.min(...tgt.m)-1.2,hi=Math.max(...tgt.m)+1.2;
        if((avg>=lo&&avg<=hi)||matches(tgt,avg))resolveAttempt(at,tgt.m[0],ts);}
      else if(ts-at.t>=240){DET.attempt=null;resolveAttempt(at,tgt.m[0],ts);}
    }
    else if(stable&&at.weak){
      DET.attempt=null;
      const fresh=at.pre===null||Math.abs(avg-at.pre)>.6;
      if(fresh&&tgt&&tgt.m.some(x=>Math.abs(x-avg)<=.6))resolveAttempt(at,avg,ts); // sinon : battement d'une note qui sonne déjà, on ignore
    }
    else if(stable){DET.attempt=null;resolveAttempt(at,avg,ts);}
    else if(ts-at.t>280)DET.attempt=null;
  }
  // note qui arrive sans attaque nette (legato) : seulement en pas à pas
  if(pitch!==null){DET.stable.push(pitch);if(DET.stable.length>5)DET.stable.shift();}else DET.stable.length=0;
  if(!DET.attempt&&S.phase==='play'&&S.mode==='wait'&&DET.stable.length>=5&&S.notes[S.pending]&&S.notes[S.pending].m.length===1&&effHand()!=='both'){
    const st=DET.stable,avg=st.reduce((a,b)=>a+b,0)/st.length;
    if(st.every(v=>Math.abs(v-avg)<.4)){
      const t=S.notes[S.pending],prev=S.notes[S.last];
      if(t&&matches(t,avg)&&!(prev&&prev.m.some(x=>pc(x)===pc(avg)))){accept(S.pending,ts);DET.stable.length=0;}
    }
  }
}
function attemptTarget(at){
  if(S.mode==='wait')return S.notes[S.pending]||null;
  const spb=1/bps();let best=null,bd=1e9;
  for(const n of S.notes){if(n.st!=='todo')continue;const d=Math.abs((at.clock-n.beat)*spb);if(d<.3&&d<bd){bd=d;best=n;}}
  return best;
}
function melodyCheck(t){return !!(t&&effHand()==='both'&&t.rh.length);}
function specRead(){if(!an2)return false;an2.getFloatFrequencyData(cbuf);return true;}
function peakMag(f){
  const bw=ctx.sampleRate/an2.fftSize,k=f/bw,a=Math.max(1,Math.floor(k*.988)),b=Math.min(cbuf.length-1,Math.ceil(k*1.012));
  let m=0;for(let i=a;i<=b;i++){const v=Math.pow(10,cbuf[i]/20);if(v>m)m=v;}return m;
}
const semi=Math.pow(2,1/12);
function trio(m){const f=440*Math.pow(2,(m-69)/12),v=x=>peakMag(x)+.5*peakMag(2*x);return {c:v(f),lo:v(f/semi),hi:v(f*semi)};}
// harmoniques 2 et 3 de la note dans la fenêtre courte (assez fines pour séparer deux demi-tons voisins)
function shortMag(m,d){
  const bw=ctx.sampleRate/an.fftSize,f=440*Math.pow(2,(m-69)/12);let s=0;
  for(const h of [2,3]){const k=Math.round(h*f/bw);let mx=0;for(let i=k-1;i<=k+1;i++)if(i>0&&i<d.length)mx=Math.max(mx,Math.pow(10,d[i]/20));s+=mx;}
  return s;
}
// La mélodie est entendue si sa note domine ses voisines d'un demi-ton et vient d'être (re)frappée.
function melodyHeard(n,base,sbase,age){
  if(!specRead())return false;
  return n.rh.every((m,i)=>{const now=trio(m),b=base?base[i]:{c:0,lo:0,hi:0};
    const dc=now.c-b.c,dl=Math.max(0,now.lo-b.lo),dh=Math.max(0,now.hi-b.hi);
    // la fenêtre longue (170 ms) ne reflète le nouveau son qu'au bout de ~150 ms : avant, on compare les hausses
    const dominant=(dc>0&&dc>=1.5*Math.max(dl,dh))||(age>=150&&now.c>=1.4*Math.max(now.lo,now.hi));
    const fresh=shortMag(m,fbuf)>=1.6*(sbase?sbase[i]:0)+1e-6;
    return dominant&&fresh;});
}
// Main gauche : chacune de ses notes doit avoir été frappée (ses harmoniques graves remontent),
// en ignorant celles qui tombent sur la mélodie (elles remontent de toute façon).
function lhParts(m,rh){
  const f=440*Math.pow(2,(m-69)/12),rf=rh.flatMap(x=>{const g=440*Math.pow(2,(x-69)/12);return [g,2*g,3*g];});
  return [1,2,3].map(h=>h*f).filter(x=>!rf.some(r=>Math.abs(r/x-1)<.02)).map(x=>peakMag(x));
}
function leftHeard(n,base){
  if(!n.lh.length)return true;
  if(!specRead()||!base)return false;
  // audible : au moins 15 % du niveau de la mélodie (en dessous : bruit de fond, ou débordement d'une note voisine)
  const ref=Math.max(...n.rh.map(m=>peakMag(440*Math.pow(2,(m-69)/12))),1e-6);
  return n.lh.every((m,i)=>{const now=lhParts(m,n.rh),b=base[i]||[];return now.some((v,k)=>v>2*(b[k]||0)&&v>=.15*ref);});
}
function pcDist(a,b){let d=((a-b)%12+12)%12;return Math.min(d,12-d);}
function matches(n,m){return n.m.some(x=>pcDist(x,m)<=.6);}

function resolveAttempt(at,m,ts){
  if(S.phase!=='play')return;
  if(S.mode==='wait'){
    const t=S.notes[S.pending];if(!t)return;
    if(matches(t,m)){accept(S.pending,ts);return;}
    if(stillRinging(m))return; // la note (ou l'accord) d'avant qui sonne encore
    if(t.m.length>1||effHand()==='both')return;
    wrong(t,m);
  }else{
    const spb=1/bps();let best=null,bd=1e9;
    for(const n of S.notes){if(n.st!=='todo')continue;const dt=(at.clock-n.beat)*spb;if(dt<-.22||dt>.28)continue;if(Math.abs(dt)<bd&&matches(n,m)){bd=Math.abs(dt);best=n;}}
    if(best){best.st='done';best.hitAt=ts;S.hits++;if(bd<.09)S.perfect++;S.last=best.i;burst(best,ts);
      flashPop(bd<.09?'Parfait':bd<.17?'Bien':'Juste',bd<.17?'var(--mint)':'var(--amber)');}
    else{if(stillRinging(m))return;S.errors++;flashPop('Raté','var(--coral)');}
  }
}
function stillRinging(m){
  const prev=S.notes[S.last];if(!prev)return false;
  if(prev.m.some(x=>pcDist(x,m)<=.6))return true;
  return prev.m.length>1&&m>=Math.min(...prev.m)-1.2&&m<=Math.max(...prev.m)+1.2;
}
function accept(i,ts){
  const n=S.notes[i];n.st='done';n.hitAt=ts;S.hits++;if(!n.slip)S.perfect++;
  S.last=i;S.pending=i+1;if(S.clock<n.beat)S.clock=n.beat;
  burst(n,ts);updateNoteCards();
}
function wrong(t,m){
  t.slip=true;S.errors++;
  const d=((m-t.m[0])%12+12)%12,up=d>6;
  showHint(`Tu joues ${nameFr(m)} · vise ${t.m.map(nameFr).join(' + ')}`,'off');
  flashPop(up?'Plus à droite →':'Plus à gauche ←','var(--coral)');
}

/* ================= Boucle ================= */
let lastTs=0;
function frame(ts){
  const dt=Math.min(.05,Math.max(0,(ts-lastTs)/1000));lastTs=ts;
  if(S.mic&&S.phase!=='demo')analyse(ts);
  update(dt,ts);
  draw(ts);updateHeard(ts);
  requestAnimationFrame(frame);
}
function update(dt,ts){
  const p=PARTS[S.sec];
  if(S.phase==='play'){
    if(S.mode==='wait'){
      const t=S.notes[S.pending];
      S.clock+=dt*bps();
      if(t&&S.clock>t.beat)S.clock=t.beat;
      if(S.loop&&(!t||t.beat>=S.loopB-1e-6)&&S.clock>=Math.min(S.loopB,S.endBeat)-.05){loopAgain();return;}
      if(!t&&S.clock>S.endBeat)finish();
    }else{
      let before=S.clock;S.clock=S.c0+(ts/1000-S.t0)*bps(); // horloge réelle : pas de dérive si l'écran rame
      if(S.loop&&S.clock>=S.loopB){const span=S.loopB-S.loopA;S.c0-=span;S.clock-=span;before=S.clock;resetLoopNotes();loopFlash();}
      if(S.clock<S.countEnd)setBig(String(Math.ceil(S.countEnd-S.clock-1e-6)));
      else if(before<S.countEnd)setBig('');
      const spb=1/bps();
      // manquée seulement après la fenêtre de jeu (0,28 s) + le temps d'analyser ce qu'on entend
      for(const n of S.notes)if(n.st==='todo'&&(S.clock-n.beat)*spb>.65){n.st='miss';}
      if(S.clock>S.endBeat)finish();
      updateNoteCards();
    }
  }else if(S.phase==='demo'){
    S.clock=demo.c0+(ctx.currentTime-demo.t0)*bps();
    while(demo.k<demo.events.length&&demo.events[demo.k].beat<=S.clock+bps()*.25){
      const e=demo.events[demo.k++];const when=demo.t0+(e.beat-demo.c0)/bps();
      e.m.forEach(m=>strike(m,Math.max(ctx.currentTime,when),e.dur/bps()*.95,e.main?.5:.28));
    }
    for(const n of S.notes)if(n.st==='todo'&&n.beat<=S.clock){n.st='lit';n.hitAt=ts;S.last=n.i;}
    updateNoteCards();
    if(S.clock>p.len+.3){demoStop();backToDemoStart();}
  }
}

/* ================= Commandes ================= */
function anchor(){S.c0=S.clock;S.t0=performance.now()/1000;}
function play(){
  if(S.phase==='demo')demoStop();
  if(S.phase==='end'||S.notes.every(n=>n.st!=='todo'))loadSection();
  if(ctx)ensureCtx();
  if(S.mode==='rhythm'&&(S.phase==='idle'||S.phase==='pause')){
    S.countEnd=Math.max(0,S.clock);S.clock=S.countEnd-BAR;
    if(ctx)for(let k=0;k<BAR;k++)click(ctx.currentTime+.03+k/bps(),k===0);
  }
  anchor();S.phase='play';renderPlay();
}
function pause(){if(S.phase==='play'){S.phase='pause';setBig('');renderPlay();}}
function togglePlay(){if(S.phase==='play')pause();else play();}
function restart(){loadSection();}
function finish(){
  if(S.phase!=='play')return;
  S.phase='end';renderPlay();setBig('');
  const total=Math.max(1,S.notes.filter(n=>n.st!=='skip').length),good=S.mode==='wait'?S.perfect:S.hits,ratio=good/total;
  const stars=ratio>=.9?3:ratio>=.7?2:ratio>=.4?1:0;
  if(!S.seeked&&!S.bassOnly){const k=S.sec+'.'+effHand(),st=saved.stars[k]=saved.stars[k]||{};st[S.mode]=Math.max(st[S.mode]||0,stars);save();renderChips();}
  const from=S.seeked?' · depuis la mesure '+Math.max(1,Math.floor((S.seekFrom-offOf())/BAR)+1):'';
  const hl={rh:'main droite',lh:'main gauche',both:'deux mains'}[effHand()]+(S.bassOnly&&effHand()!=='rh'?' (basses seules)':'');
  $('endSec').textContent=PARTS[S.sec].name+' · '+hl+' · '+Math.round(S.speed*100)+' %'+from;
  $('endStars').innerHTML='★'.repeat(stars)+'<i>'+'★'.repeat(3-stars)+'</i>';
  $('endScore').innerHTML=(S.mode==='wait'?`${good} / ${total} notes du premier coup`:`${good} / ${total} notes en rythme`)+
    `<small>${stars===3?(S.mode==='wait'?'Prêt pour le mode « En rythme ».':'Essaie un peu plus vite.'):stars>=1?'Encore une fois, ça rentre.':'Ralentis un peu, ça va venir.'}</small>`;
  const idx=SECTION_IDS.indexOf(S.sec);
  $('endNext').hidden=idx>=SECTION_IDS.length-1;
  $('endFaster').textContent=S.speed>=1.2?'Vitesse max':`Plus vite (${Math.round(Math.min(1.2,S.speed+.1)*100)} %)`;
  $('endFaster').disabled=S.speed>=1.2;
  $('endOv').hidden=false;
  setTimeout(()=>$('endAgain').focus(),50);
}
function hideEnd(){$('endOv').hidden=true;}

const demo={events:[],k:0,t0:0,c0:0};
function demoStart(){
  ensureCtx();
  if(S.phase==='demo'){demoStop();backToDemoStart();return;}
  const from=(S.phase==='idle'||S.phase==='pause')&&S.seeked?Math.max(0,S.clock):0;
  loadSection();if(from>0)seekTo(from);
  const p=PARTS[S.sec];
  demo.events=[...p.rh.map(n=>({...n,main:effHand()!=='lh'})),...p.lh.map(n=>({...n,main:effHand()!=='rh'}))]
    .sort((a,b)=>a.beat-b.beat);
  if(S.sec==='tout'){ // la liste « main droite » de Tout contient déjà l'intro : on ne la double pas
    const ids=new Set();demo.events=demo.events.filter(e=>{const key=e.beat+'|'+e.m.join();if(ids.has(key))return false;ids.add(key);return true;});
  }
  demo.from=from;demo.k=demo.events.findIndex(e=>e.beat>=from-.01);if(demo.k<0)demo.k=demo.events.length;
  demo.c0=from-1;demo.t0=ctx.currentTime+.05;S.clock=demo.c0;S.phase='demo';renderPlay();
}
function backToDemoStart(){loadSection();if(demo.from>0)seekTo(demo.from);}
function demoStop(){
  if(S.phase==='demo'){voices.forEach(v=>{try{v.stop();}catch(e){}});voices.clear();S.phase='idle';DET.mute=performance.now()+400;renderPlay();}
}

/* ================= Rendu : notes qui tombent + clavier ================= */
const cv=$('hw'),c2=cv.getContext('2d');let W=0,H=0,DPR=1;
function resize(){
  DPR=Math.min(2,window.devicePixelRatio||1);
  const r=cv.getBoundingClientRect();W=r.width;H=r.height;cv.width=Math.round(W*DPR);cv.height=Math.round(H*DPR);
}
function geo(){
  const kbH=Math.max(70,Math.min(150,H*.26)),hitY=H-kbH;
  const whites=[];for(let m=S.lo;m<=S.hi;m++)if(!isBlack(m))whites.push(m);
  const ww=W/whites.length,bw=ww*.6;
  const wIdx={};whites.forEach((m,i)=>wIdx[m]=i);
  const keyX=m=>isBlack(m)?wIdx[m+1]*ww-bw/2:wIdx[m]*ww; // gauche de la touche
  const keyW=m=>isBlack(m)?bw:ww;
  const ppb=Math.max(48,Math.min(150,hitY/5.2));
  return {kbH,hitY,whites,ww,bw,keyX,keyW,ppb,y:b=>hitY-(b-S.clock)*ppb};
}
function rr(C,x,y,w,h,r){r=Math.min(r,w/2,h/2);C.beginPath();C.moveTo(x+r,y);C.arcTo(x+w,y,x+w,y+h,r);C.arcTo(x+w,y+h,x,y+h,r);C.arcTo(x,y+h,x,y,r);C.arcTo(x,y,x+w,y,r);C.closePath();}
const parts=[];
function burst(n,ts){
  const g=geo();
  n.m.forEach(m=>{const x=g.keyX(m)+g.keyW(m)/2;S.keyFx[m]=ts;
    for(let k=0;k<16;k++){const a=-Math.PI*(.1+.8*Math.random()),v=60+Math.random()*170;
      parts.push({x,y:g.hitY,vx:Math.cos(a)*v,vy:Math.sin(a)*v,t:ts,c:Math.random()<.5?'#ffc53d':'#3ddc97'});}});
}
function nextTodo(){for(const n of S.notes)if(n.st==='todo')return n.i;return -1;}
function draw(ts){
  const g=geo(),C=c2;C.setTransform(DPR,0,0,DPR,0,0);C.clearRect(0,0,W,H);
  // couloirs des touches noires (repère discret)
  C.fillStyle='rgba(255,255,255,.018)';
  for(let m=S.lo;m<=S.hi;m++)if(isBlack(m))C.fillRect(g.keyX(m),0,g.bw,g.hitY);
  // mesures
  const b0=Math.floor(S.clock),b1=Math.ceil(S.clock+g.hitY/g.ppb);
  const o=offOf();
  for(let b=b0;b<=b1;b++){if(b<o||(((b-o)%BAR)+BAR)%BAR)continue;const y=g.y(b);if(y<0||y>g.hitY)continue;
    C.fillStyle='rgba(174,183,196,.12)';C.fillRect(0,y,W,1);
    if(b<PARTS[S.sec].len){C.fillStyle='rgba(139,148,165,.6)';C.font='600 11px Inter,system-ui,sans-serif';C.textAlign='left';C.textBaseline='bottom';C.fillText(String((b-o)/BAR+1),6,y-3);}}
  // notes
  const pend=S.mode==='wait'?S.pending:nextTodo();
  C.save();C.beginPath();C.rect(0,0,W,g.hitY);C.clip();
  for(const n of S.notes){
    const yb=g.y(n.beat);
    if(yb-n.dur*g.ppb>g.hitY+40||yb<-10)continue;
    const isPend=S.phase!=='demo'&&n.i===pend&&n.st==='todo';
    const age=n.hitAt?Math.min(1,(ts-n.hitAt)/600):0;
    n.parts.forEach(part=>{const h=Math.max(10,part.dur*g.ppb-4),yt=yb-h,left=part.hand==='lh';
    part.m.forEach(m=>{
      const blk=isBlack(m),x=g.keyX(m)+(blk?1:2.5),w=g.keyW(m)-(blk?2:5);
      let fill,txt=left?'#061a2e':'#1b1404',stroke=null;
      if(n.st==='done'){fill='rgba(61,220,151,'+(1-age*.6)+')';txt='#06210f';}
      else if(n.st==='lit')fill='rgba(255,224,138,'+(1-age*.5)+')';
      else if(n.st==='skip'){fill=left?'rgba(108,184,255,.2)':'rgba(255,197,61,.2)';txt='rgba(10,14,20,.55)';}
      else if(n.st==='miss'){fill='rgba(255,107,107,.16)';stroke='#ff6b6b';txt='#ff9a9a';}
      else fill=left?(blk?'#4a9fe6':'#6cb8ff'):(blk?'#e8a91f':'#ffc53d');
      if(isPend){const pulse=.5+.5*Math.sin(ts/170);C.shadowColor='rgba(255,224,138,.9)';C.shadowBlur=12+10*pulse;}
      rr(C,x,yt,w,h-1,Math.min(7,w/3));C.fillStyle=fill;C.fill();C.shadowBlur=0;
      if(stroke){C.strokeStyle=stroke;C.lineWidth=1.5;C.stroke();}
      if(isPend){C.strokeStyle='#fff';C.lineWidth=2;C.stroke();}
      if(w>=13){const fs=Math.round(Math.min(15,w*.55));C.fillStyle=txt;C.font=`700 ${fs}px Rubik,system-ui,sans-serif`;C.textAlign='center';C.textBaseline='bottom';
        C.fillText(nameEn(m),x+w/2,yb-Math.max(3,Math.min(6,h*.15)));}
    });});
  }
  C.restore();
  // boucle : bande verte sur le bord gauche entre le début et la fin
  if(S.loop){const ya=g.y(S.loopA),yb2=g.y(S.loopB),t=Math.max(0,yb2),bo=Math.min(g.hitY,ya);
    if(bo>t){C.fillStyle='rgba(61,220,151,.07)';C.fillRect(0,t,W,bo-t);C.fillStyle='#3ddc97';C.fillRect(0,t,4,bo-t);}
    C.fillStyle='rgba(61,220,151,.7)';[ya,yb2].forEach(y=>{if(y>=0&&y<=g.hitY)for(let x=0;x<W;x+=12)C.fillRect(x,y,6,1.5);});}
  // rail de position dans la partie
  {const top=10,bot=g.hitY-10,len=S.endBeat+2,fr=Math.max(0,Math.min(1,(S.clock+2)/len)),th=Math.max(22,(bot-top)*Math.min(1,(g.hitY/g.ppb)/len));
   const y=bot-th-(bot-top-th)*fr;C.fillStyle='rgba(174,183,196,.12)';rr(C,W-7,top,4,bot-top,2);C.fill();
   C.fillStyle=drag.moved&&drag.id!==null?'#ffc53d':'rgba(174,183,196,.45)';rr(C,W-7,y,4,th,2);C.fill();}
  // ligne d'arrivée
  const lg=C.createLinearGradient(0,g.hitY-26,0,g.hitY);lg.addColorStop(0,'rgba(255,197,61,0)');lg.addColorStop(1,'rgba(255,197,61,.22)');
  C.fillStyle=lg;C.fillRect(0,g.hitY-26,W,26);
  drawKeyboard(g,ts);
  for(let k=parts.length-1;k>=0;k--){const p=parts[k];const t=(ts-p.t)/1000;if(t>.7){parts.splice(k,1);continue;}
    C.globalAlpha=1-t/.7;C.fillStyle=p.c;C.beginPath();C.arc(p.x+p.vx*t,p.y+p.vy*t+140*t*t,2.4,0,Math.PI*2);C.fill();}
  C.globalAlpha=1;
}
function drawKeyboard(g,ts){
  const C=c2,top=g.hitY,kh=g.kbH,cur=currentNote(),want=new Set(cur&&S.phase!=='demo'?cur.m:[]),lhKeys=new Set(cur&&S.phase!=='demo'?cur.lh:[]);
  const fx=m=>{const t=S.keyFx[m];return t&&ts-t<320?1-(ts-t)/320:0;};
  C.fillStyle='#ffc53d';C.fillRect(0,top-2,W,2);
  // touches blanches
  g.whites.forEach(m=>{
    const x=g.keyX(m),w=g.ww,f=fx(m);
    C.fillStyle=f>0?`rgba(61,220,151,${.5+.5*f})`:want.has(m)?(lhKeys.has(m)?'#9fd0ff':'#ffd666'):'#f2f0ea';
    rr(C,x+1,top,w-2,kh-2,4);C.fill();
    if(f===0&&!want.has(m)){C.fillStyle='rgba(0,0,0,.08)';C.fillRect(x+1,top+kh-12,w-2,10);}
    if(pc(m)===0&&g.ww>=18){C.fillStyle=m===60?'#c26d00':'#8b8478';C.font=`600 ${Math.min(12,g.ww*.42)}px Inter,system-ui,sans-serif`;C.textAlign='center';C.textBaseline='bottom';
      C.fillText('Do',x+w/2,top+kh-8);}
    if(m===60){C.fillStyle='#c26d00';C.beginPath();C.arc(x+w/2,top+kh-(g.ww>=18?26:10),3,0,Math.PI*2);C.fill();}
    if(want.has(m)&&f===0){C.fillStyle='#1b1404';C.font=`700 ${Math.min(15,g.ww*.5)}px Rubik,system-ui,sans-serif`;C.textAlign='center';C.textBaseline='middle';
      C.fillText(nameEn(m),x+w/2,top+kh*.72);}
  });
  // touches noires
  for(let m=S.lo;m<=S.hi;m++){if(!isBlack(m))continue;
    const x=g.keyX(m),w=g.bw,h=kh*.62,f=fx(m);
    C.fillStyle=f>0?`rgba(61,220,151,${.6+.4*f})`:want.has(m)?(lhKeys.has(m)?'#4a9fe6':'#ffc53d'):'#1a1d23';
    rr(C,x,top,w,h,3);C.fill();
    if(!want.has(m)&&f===0){C.fillStyle='rgba(255,255,255,.08)';C.fillRect(x+3,top+h-8,w-6,4);}
  }
  // démo : touches qui sonnent
  if(S.phase==='demo'){for(const n of S.notes)if(n.st==='lit'&&ts-n.hitAt<220)n.m.forEach(m=>{const x=g.keyX(m),w=g.keyW(m);C.fillStyle='rgba(255,197,61,.55)';rr(C,x+1,top,w-2,isBlack(m)?kh*.62:kh-2,4);C.fill();});}
}

/* ================= Boucle sur 1 ou 2 mesures ================= */
function setLoopAt(b){
  const len=PARTS[S.sec].len,o=offOf();let a=b<o?0:o+Math.floor((b-o)/BAR)*BAR;
  if(a>=len)a=Math.max(0,len-BAR);
  S.loopA=a;S.loopB=Math.min(len,(a<o?o:a)+BAR*S.loop); // depuis le début : l'anacrouse est incluse
}
function resetLoopNotes(){S.notes.forEach(n=>{if(n.beat>=S.loopA-1e-6&&n.beat<S.loopB-1e-6){n.st='todo';n.slip=false;n.hitAt=0;}});}
function loopFlash(){S.loops++;flashPop('Encore · tour '+(S.loops+1),'var(--mint)');}
function loopAgain(){
  resetLoopNotes();
  S.pending=S.notes.findIndex(n=>n.st==='todo');if(S.pending<0)S.pending=S.notes.length;
  S.last=-1;S.clock=S.loopA-1;DET.attempt=null;loopFlash();updateNoteCards(true);
}
function toggleLoop(){
  S.loop=S.loop===0?1:S.loop===1?2:0;
  if(S.loop){setLoopAt(S.phase==='play'?S.clock:S.clock);if(S.phase!=='play')seekTo(S.loopA,false,true);}
  renderPlay();
}

/* ================= Parcourir la partition ================= */
function clampClock(b){return Math.max(-2,Math.min(S.endBeat-.5,b));}
// Repart de la position b : les notes d'avant sont mises de côté, celles d'après sont à jouer.
function seekTo(b,snap,keepLoop){
  b=clampClock(b);
  if(snap){let best=null,bd=1.01;for(const n of S.notes){const d=Math.abs(n.beat-b);if(d<bd){bd=d;best=n;}}if(best)b=best.beat;}
  if(b<=0.01&&!snap){b=Math.min(b,0);}
  S.clock=b;
  S.notes.forEach(n=>{n.st=n.beat<b-.01?'skip':'todo';n.slip=false;n.hitAt=0;});
  S.pending=S.notes.findIndex(n=>n.st==='todo');if(S.pending<0)S.pending=S.notes.length;
  S.last=-1;S.hits=0;S.perfect=0;S.errors=0;S.keyFx={};DET.attempt=null;
  S.seeked=b>.01;S.seekFrom=Math.max(0,b);S.countEnd=0;
  if(S.phase!=='pause')S.phase='idle';
  if(S.loop&&!keepLoop){setLoopAt(b);}
  S.loops=0;
  setBig('');cardKey='';updateNoteCards(true);renderPlay();
}
// Glisser au doigt ou à la souris (la partition suit le doigt), molette, flèches haut/bas.
const drag={id:null,y0:0,c0:0,moved:false};
function stopForScroll(){if(S.phase==='play')pause();else if(S.phase==='demo'){demoStop();}}
cv.addEventListener('pointerdown',e=>{
  if(S.phase==='end')return;
  drag.id=e.pointerId;drag.y0=e.clientY;drag.c0=S.clock;drag.moved=false;
  try{cv.setPointerCapture(e.pointerId);}catch(_){}
});
cv.addEventListener('pointermove',e=>{
  if(drag.id!==e.pointerId)return;
  const dy=e.clientY-drag.y0;
  if(!drag.moved&&Math.abs(dy)<6)return;
  if(!drag.moved){drag.moved=true;stopForScroll();drag.c0=S.clock;drag.y0=e.clientY;cv.classList.add('dragging');return;}
  S.clock=clampClock(drag.c0+dy/geo().ppb);
});
function endDrag(e){
  if(drag.id!==e.pointerId)return;
  drag.id=null;cv.classList.remove('dragging');
  if(drag.moved)seekTo(S.clock,true);else manualHit();
}
cv.addEventListener('pointerup',endDrag);cv.addEventListener('pointercancel',endDrag);
let wheelT=0;
cv.addEventListener('wheel',e=>{
  if(S.phase==='end')return;
  e.preventDefault();stopForScroll();
  const px=e.deltaMode===1?e.deltaY*16:e.deltaMode===2?e.deltaY*H:e.deltaY;
  S.clock=clampClock(S.clock-px/geo().ppb);
  clearTimeout(wheelT);wheelT=setTimeout(()=>seekTo(S.clock,true),180);
},{passive:false});

/* ================= Cartes ================= */
function currentNote(){
  if(S.phase==='demo'){return S.notes[Math.max(0,S.last)]||S.notes[0];}
  if(S.mode==='wait')return S.notes[Math.min(S.pending,S.notes.length-1)];
  const k=nextTodo();return S.notes[k>=0?k:S.notes.length-1];
}
function octTxt(m){
  const o=Math.floor((m-60)/12);
  if(o===0)return 'à droite du Do central';
  if(o===-1)return 'à gauche du Do central';
  return o>0?`${o} octave${o>1?'s':''} à droite du Do central`:`${-o-1} octave${-o-1>1?'s':''} à gauche du Do central`;
}
let cardKey='';
function updateNoteCards(force){
  const n=currentNote();if(!n)return;
  const nx=S.notes[n.i+1];
  const key=n.i+'|'+S.phase;if(key===cardKey&&!force)return;cardKey=key;
  const names=a=>a.map(nameFr).join(' + ');
  if(n.hand==='both'){
    $('tNote').innerHTML=`${names(n.rh)}<small style="color:var(--lh)">${names(n.lh)}</small>`;
    $('tWhere').innerHTML=`Ensemble : droite <b>${names(n.rh)}</b> · gauche <b style="color:var(--lh)">${names(n.lh)}</b>`;
  }else{
    $('tNote').innerHTML=names(n.m)+`<small>${n.m.map(nameEn).join('+')}</small>`;
    $('tWhere').textContent=(n.hand==='lh'?'Main gauche':'Main droite')+' · '+(n.m.length>1?'ensemble, ':'')+octTxt(Math.min(...n.m));
  }
  $('tNext').textContent=nx?'Ensuite : '+(nx.hand==='both'?names(nx.rh)+' + '+names(nx.lh)+' (ensemble)':names(nx.m)):'Dernière note';
}
let heardShownAt=0;
function updateHeard(ts){
  if(!S.mic)return;
  const lv=Math.min(1,Math.sqrt(DET.rms/.12));$('lvl').style.height=(lv*100)+'%';
  $('gateMark').style.bottom=(Math.min(1,Math.sqrt(gate()/.12))*100)+'%';
  const h=DET.hist;let m=null;if(h.length){const a=[...h].sort((x,y)=>x-y);m=a[a.length>>1];}
  const el=$('hNote');
  if(m!==null){heardShownAt=ts;el.textContent=nameFr(m);
    const t=S.phase==='play'?currentNote():null;
    if(t){const ok=matches(t,m);el.className='heard-note '+(ok?'ok':'off');if(ok)showHint('C’est ça','ok');}
    else el.className='heard-note';
  }else if(ts-heardShownAt>900){el.textContent='…';el.className='heard-note';}
}
let hintT=0;
function showHint(t,cls){const el=$('hHint');el.textContent=t;el.className='hint '+(cls||'');clearTimeout(hintT);hintT=setTimeout(()=>{el.textContent='';el.className='hint';},1600);}
let popT=0;
function flashPop(t,color){const el=$('pop');el.textContent=t;el.style.color=color;el.classList.add('on');clearTimeout(popT);popT=setTimeout(()=>el.classList.remove('on'),650);}
function setBig(t){$('big').textContent=t;}

/* ================= Interface ================= */
function $(id){return document.getElementById(id);}
const IC={
  play:'<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M7 4.5v15l13-7.5z"/></svg>',
  pause:'<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><rect x="6" y="4.5" width="4.2" height="15" rx="1"/><rect x="13.8" y="4.5" width="4.2" height="15" rx="1"/></svg>',
  restart:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 12a8 8 0 1 0 2.4-5.7"/><path d="M4 4v4.5h4.5"/></svg>',
  ear:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 9v6h4l5 4V5L8 9z"/><path d="M16.5 8.5a5 5 0 0 1 0 7"/><path d="M19 6a8.5 8.5 0 0 1 0 12"/></svg>',
  stop:'<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><rect x="6" y="6" width="12" height="12" rx="2"/></svg>',
  loop:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 11V9a3 3 0 0 1 3-3h12"/><path d="M16 3l3 3-3 3"/><path d="M20 13v2a3 3 0 0 1-3 3H5"/><path d="M8 21l-3-3 3-3"/></svg>'
};
function renderPlay(){
  const playing=S.phase==='play';
  $('scrollHint').style.opacity=(S.phase==='idle'||S.phase==='pause')?'1':'0';
  $('playIc').innerHTML=playing?IC.pause:IC.play;
  $('playTx').textContent=playing?'Pause':(S.phase==='pause'?'Reprendre':'Jouer');
  $('listenBtn').innerHTML=(S.phase==='demo'?IC.stop+'Arrêter':IC.ear+'Écouter');
  $('mWait').setAttribute('aria-pressed',S.mode==='wait');$('mRhythm').setAttribute('aria-pressed',S.mode==='rhythm');
  const h=effHand(),rhOk=PARTS[S.sec].rh.length>0;
  $('hRight').setAttribute('aria-pressed',h==='rh');$('hLeft').setAttribute('aria-pressed',h==='lh');$('hBoth').setAttribute('aria-pressed',h==='both');
  $('hRight').disabled=!rhOk;$('hBoth').disabled=!rhOk;
  $('hRight').title=$('hBoth').title=rhOk?'':'L’intro se joue à la main gauche';
  $('bassBtn').hidden=h==='rh';$('bassBtn').setAttribute('aria-pressed',S.bassOnly);
  $('loopBtn').setAttribute('aria-pressed',S.loop>0);
  $('loopBtn').innerHTML=IC.loop+(S.loop?`Boucle ${S.loop} mesure${S.loop>1?'s':''}`:'Boucle');
  const pct=Math.round(S.speed*100);
  $('speedOut').innerHTML=`<b>${pct} %</b><small>${Math.round(BPM*S.speed)} BPM</small>`;
}
function renderChips(){
  const box=$('chips');box.innerHTML='';
  SECTION_IDS.forEach((id,i)=>{
    const b=document.createElement('button');b.type='button';b.className='chip';b.setAttribute('aria-pressed',id===S.sec);
    let best=0;['rh','lh','both'].forEach(h=>{const st=saved.stars[id+'.'+h]||{};best=Math.max(best,st.wait||0,st.rhythm||0);});
    b.innerHTML=(id==='tout'?'':`<span class="num">${i+1}</span>`)+`<span>${PARTS[id].name}</span>`+
      (best?`<span class="st">${'★'.repeat(best)}<i>${'★'.repeat(3-best)}</i></span>`:'');
    b.addEventListener('click',()=>{S.sec=id;saved.sec=id;save();loadSection();});
    box.appendChild(b);
  });
  const on=box.querySelector('[aria-pressed="true"]');
  if(on){const l=on.offsetLeft-box.offsetLeft,r=l+on.offsetWidth;if(l<box.scrollLeft||r>box.scrollLeft+box.clientWidth)box.scrollLeft=Math.max(0,l-24);}
}
function setMode(m){if(S.mode===m)return;S.mode=m;saved.mode=m;save();loadSection();}
function setHand(h){S.hand=h;saved.hand=h;save();loadSection();}
function setSpeed(v){S.speed=Math.round(Math.min(1.2,Math.max(.3,v))*20)/20;saved.speed=S.speed;save();anchor();
  if(S.phase==='demo'){demoStop();loadSection();}renderPlay();}

$('restartBtn').innerHTML=IC.restart;
$('playBtn').addEventListener('click',togglePlay);
$('restartBtn').addEventListener('click',restart);
$('listenBtn').addEventListener('click',demoStart);
$('hRight').addEventListener('click',()=>setHand('rh'));
$('hLeft').addEventListener('click',()=>setHand('lh'));
$('hBoth').addEventListener('click',()=>setHand('both'));
$('bassBtn').addEventListener('click',()=>{S.bassOnly=!S.bassOnly;saved.bassOnly=S.bassOnly;save();loadSection();});
$('loopBtn').addEventListener('click',toggleLoop);
$('mWait').addEventListener('click',()=>setMode('wait'));
$('mRhythm').addEventListener('click',()=>setMode('rhythm'));
$('slower').addEventListener('click',()=>setSpeed(S.speed-.05));
$('faster').addEventListener('click',()=>setSpeed(S.speed+.05));
$('sens').value=S.sens;$('sens').addEventListener('input',e=>{S.sens=+e.target.value;saved.sens=S.sens;save();});
$('endAgain').addEventListener('click',()=>{loadSection();play();});
$('endFaster').addEventListener('click',()=>{setSpeed(S.speed+.1);loadSection();play();});
$('endNext').addEventListener('click',()=>{const i=SECTION_IDS.indexOf(S.sec);S.sec=SECTION_IDS[Math.min(SECTION_IDS.length-1,i+1)];saved.sec=S.sec;save();loadSection();});

// Sans micro : un toucher sur l'écran (ou Entrée) joue la bonne note.
function manualHit(){if(!S.manual||S.phase!=='play')return;const ts=performance.now();
  if(S.mode==='wait'){if(S.notes[S.pending])accept(S.pending,ts);}
  else{const n=S.notes[nextTodo()];if(n)resolveAttempt({clock:S.clock},n.m[0],ts);}}

document.addEventListener('keydown',e=>{
  if(e.target.tagName==='INPUT')return;
  if(!$('startOv').hidden)return;
  if(e.code==='Space'){e.preventDefault();if(!$('endOv').hidden){hideEnd();loadSection();play();}else togglePlay();}
  else if(e.key==='r'||e.key==='R')restart();
  else if(e.key==='ArrowUp'||e.key==='ArrowDown'){e.preventDefault();if(!$('endOv').hidden)return;stopForScroll();seekTo(S.clock+(e.key==='ArrowUp'?1:-1),true);}
  else if(e.key==='Enter'&&S.manual){e.preventDefault();manualHit();}
});
document.addEventListener('visibilitychange',()=>{if(document.hidden){pause();if(S.phase==='demo'){demoStop();loadSection();}}});

let wakeLock=null;
async function keepAwake(){
  try{if(!wakeLock&&navigator.wakeLock&&document.visibilityState==='visible'){wakeLock=await navigator.wakeLock.request('screen');wakeLock.addEventListener('release',()=>{wakeLock=null;});}}catch(e){}
}
document.addEventListener('visibilitychange',()=>{if(!document.hidden&&S.mic)keepAwake();});
$('goBtn').addEventListener('click',async()=>{
  ensureCtx();
  try{await startMic();$('startOv').hidden=true;keepAwake();}
  catch(err){
    const e=$('startErr');e.hidden=false;
    e.textContent=location.protocol==='http:'?'Le micro n’est disponible qu’en https ou en ouvrant le fichier directement.':'Le micro a été refusé. Autorise-le dans la barre d’adresse, puis réessaie.';
    $('goBtn').textContent='Réessayer';$('noMicBtn').hidden=false;
  }
});
$('noMicBtn').addEventListener('click',()=>{S.manual=true;$('startOv').hidden=true;$('hNote').textContent='—';$('hHint').textContent='Sans micro : touche l’écran au bon moment.';});

window.addEventListener('resize',resize);
if(window.ResizeObserver)new ResizeObserver(resize).observe($('stage'));
resize();loadSection();renderPlay();requestAnimationFrame(frame);
window.__rushE={state:S,det:DET};
};
