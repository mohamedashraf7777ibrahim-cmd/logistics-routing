(function(){
var cv=document.getElementById('map'),ctx=cv.getContext('2d');
var COLS=7,ROWS=5,X0=50,Y0=50,DX=90,DY=80,N=COLS*ROWS,DEPOT=28;
var jam={},zones=[],stops=[9,19,24],showNaive=false,raf=0;
function pos(n){return [X0+(n%COLS)*DX,Y0+Math.floor(n/COLS)*DY]}
function ek(a,b){return a<b?a+'-'+b:b+'-'+a}
function md(a,b){return Math.abs(Math.floor(a/COLS)-Math.floor(b/COLS))+Math.abs(a%COLS-b%COLS)}
var edges=[],adj=[];for(var i=0;i<N;i++)adj[i]=[];
for(var r=0;r<ROWS;r++)for(var c=0;c<COLS;c++){var n=r*COLS+c;
if(c<COLS-1){edges.push([n,n+1]);adj[n].push(n+1);adj[n+1].push(n)}
if(r<ROWS-1){edges.push([n,n+COLS]);adj[n].push(n+COLS);adj[n+COLS].push(n)}}
function rw(a,b){return jam[ek(a,b)]?4:1}
function fw(){return 1}
function dij(s,wf){var d=[],pv=[],done=[];for(var i=0;i<N;i++){d[i]=1e9;pv[i]=-1}
d[s]=0;for(var k=0;k<N;k++){var u=-1;for(var i=0;i<N;i++)if(!done[i]&&(u<0||d[i]<d[u]))u=i;
done[u]=1;adj[u].forEach(function(v){var nd=d[u]+wf(u,v);if(nd<d[v]){d[v]=nd;pv[v]=u}})}
return {d:d,pv:pv}}
function pathTo(pv,t){var p=[t];while(pv[p[0]]>=0)p.unshift(pv[p[0]]);return p}
function perms(a){if(a.length<2)return [a];var o=[];a.forEach(function(x,i){perms(a.slice(0,i).concat(a.slice(i+1))).forEach(function(p){o.push([x].concat(p))})});return o}
function plan(wf){var pts=[DEPOT].concat(stops),R=pts.map(function(s){return dij(s,wf)});
var idx=stops.map(function(_,i){return i+1}),best=null,bc=1e18;
perms(idx).forEach(function(p){var seq=[0].concat(p,[0]),cc=0;
for(var i=0;i<seq.length-1;i++)cc+=R[seq[i]].d[pts[seq[i+1]]];
if(cc<bc){bc=cc;best=seq}});
var path=[DEPOT];for(var i=0;i<best.length-1;i++){path=path.concat(pathTo(R[best[i]].pv,pts[best[i+1]]).slice(1))}
return path}
function pc(p){var s=0;for(var i=0;i<p.length-1;i++)s+=rw(p[i],p[i+1]);return s}
function jc(p){var s=0;for(var i=0;i<p.length-1;i++)if(jam[ek(p[i],p[i+1])])s++;return s}
var reduce=matchMedia('(prefers-reduced-motion:reduce)').matches;
var W=0,Hh=0,dpr=1,tk=0,yawU=.55,pit=1.0,yaw=.55,gcs=1,gsn=0,gcp=1,gsp=0,F=1,drag=null,moved=0,vis=true,sm=null,nv=null,NP=[],vp=[],vtot=0,loopRaf=0;
function wp(n){return [n%COLS-3,Math.floor(n/COLS)-2]}
var sd=7;function rnd(){sd|=0;sd=sd+0x6D2B79F5|0;var q=Math.imul(sd^sd>>>15,1|sd);q=q+Math.imul(q^q>>>7,61|q)^q;return((q^q>>>14)>>>0)/4294967296}
var BL=[];for(var br=0;br<ROWS-1;br++)for(var bc=0;bc<COLS-1;bc++){var bx0=bc-3+.17,bz0=br-2+.17,bs=.66,pt=rnd(),bk=pt<.3?1:pt<.65?2:4,bd=Math.hypot(bc-2.5,br-1.5);
var rc=bk===1?[[0,0,1,1]]:bk===2?(rnd()<.5?[[0,0,.48,1],[.52,0,.48,1]]:[[0,0,1,.48],[0,.52,1,.48]]):[[0,0,.48,.48],[.52,0,.48,.48],[0,.52,.48,.48],[.52,.52,.48,.48]];
rc.forEach(function(q){var h=((.12+rnd()*.5)*(1.5-bd*.17)+(rnd()<.12?.3:0))*.72;BL.push({x:bx0+(q[0]+q[2]/2)*bs,z:bz0+(q[1]+q[3]/2)*bs,w:q[2]*bs,d:q[3]*bs,h:Math.max(.1,h),rgb:[24+rnd()*22,62+rnd()*40,122+rnd()*50]})})}
function P(x,y,z){var x1=x*gcs-z*gsn,z1=x*gsn+z*gcs,yv=y*gcp-z1*gsp,zv=y*gsp+z1*gcp,dp=12-zv,k=F/dp;return [W/2+x1*k,Hh*.54-yv*k,dp,k]}
function shd(c,s){return 'rgb('+Math.round(Math.min(255,c[0]*s))+','+Math.round(Math.min(255,c[1]*s))+','+Math.round(Math.min(255,c[2]*s))+')'}
function poly(pts,fill,stroke){ctx.beginPath();pts.forEach(function(p,i){i?ctx.lineTo(p[0],p[1]):ctx.moveTo(p[0],p[1])});ctx.closePath();ctx.fillStyle=fill;ctx.fill();if(stroke){ctx.strokeStyle=stroke;ctx.lineWidth=1*dpr;ctx.stroke()}}
var LX=-.507,LZ=.862;
function boxItem(x,z,w,d,h,ang,rgb,glow){return {dep:P(x,0,z)[2],draw:function(){
var cs=Math.cos(ang),sn=Math.sin(ang),hw=w/2,hd=d/2,cr=[[-hw,-hd],[hw,-hd],[hw,hd],[-hw,hd]].map(function(p){return [x+p[0]*cs-p[1]*sn,z+p[0]*sn+p[1]*cs]});
var bt=cr.map(function(p){return P(p[0],0,p[1])}),tp=cr.map(function(p){return P(p[0],h,p[1])}),fc=[];
for(var i=0;i<4;i++){var j=(i+1)%4,dx=cr[j][0]-cr[i][0],dz=cr[j][1]-cr[i][1],ln=Math.hypot(dx,dz)||1;fc.push({dep:(bt[i][2]+bt[j][2]+tp[i][2]+tp[j][2])/4,pts:[bt[i],bt[j],tp[j],tp[i]],s:.4+.6*Math.max(0,(dz/ln)*LX+(-dx/ln)*LZ)})}
fc.sort(function(a,b){return b.dep-a.dep});
if(glow){ctx.shadowColor=glow;ctx.shadowBlur=14*dpr}
fc.forEach(function(f){poly(f.pts,shd(rgb,f.s),'rgba(130,170,255,.2)')});poly(tp,shd(rgb,1.3),'rgba(160,195,255,.35)');ctx.shadowBlur=0}}}
function prep(){var cs=Math.cos(yaw),sn=Math.sin(yaw);gcs=cs;gsn=sn;gcp=Math.cos(pit);gsp=Math.sin(pit);F=W*1.06}
function lineP(nodes,y){ctx.beginPath();nodes.forEach(function(n,i){var w=wp(n),p=P(w[0],y,w[1]);i?ctx.lineTo(p[0],p[1]):ctx.moveTo(p[0],p[1])})}
function frame(){
tk++;yaw=yawU+(reduce?0:Math.sin(tk*.0035)*.22);prep();
var bg=ctx.createLinearGradient(0,0,0,Hh);bg.addColorStop(0,'#0c1c4c');bg.addColorStop(1,'#050b20');ctx.fillStyle=bg;ctx.fillRect(0,0,W,Hh);
for(var n=0;n<N;n++){var w0=wp(n),p0=P(w0[0],0,w0[1]);NP[n]=[p0[0]/dpr,p0[1]/dpr]}
var gp=[[-3.75,-2.75],[3.75,-2.75],[3.75,2.75],[-3.75,2.75]].map(function(q){return P(q[0],0,q[1])});
ctx.shadowColor='#2979ff';ctx.shadowBlur=18*dpr;poly(gp,'#0a1634','rgba(60,120,255,.55)');ctx.shadowBlur=0;
zones.forEach(function(z){var c=wp(z),ring=[];for(var i=0;i<48;i++){var a=i/48*6.2832;ring.push(P(c[0]+Math.cos(a)*1.45,.01,c[1]+Math.sin(a)*1.45))}
poly(ring,'rgba(255,93,93,.13)','rgba(255,93,93,.55)')});
edges.forEach(function(e){var a=wp(e[0]),b=wp(e[1]),dx=b[0]-a[0],dz=b[1]-a[1],ln=Math.hypot(dx,dz),px=-dz/ln*.085,pz=dx/ln*.085,j=jam[ek(e[0],e[1])];
if(j){ctx.shadowColor='#ff5d5d';ctx.shadowBlur=14*dpr}
poly([P(a[0]+px,.005,a[1]+pz),P(b[0]+px,.005,b[1]+pz),P(b[0]-px,.005,b[1]-pz),P(a[0]-px,.005,a[1]-pz)],j?'#ff5d5d':'#2a427f');ctx.shadowBlur=0});
for(var m=0;m<N;m++){var c2=wp(m);poly([P(c2[0]-.085,.006,c2[1]-.085),P(c2[0]+.085,.006,c2[1]-.085),P(c2[0]+.085,.006,c2[1]+.085),P(c2[0]-.085,.006,c2[1]+.085)],'#2a427f')}
ctx.strokeStyle='rgba(160,185,235,.28)';ctx.lineWidth=1*dpr;ctx.setLineDash([5*dpr,6*dpr]);
edges.forEach(function(e){if(jam[ek(e[0],e[1])])return;var a=wp(e[0]),b=wp(e[1]),p=P(a[0],.008,a[1]),q=P(b[0],.008,b[1]);ctx.beginPath();ctx.moveTo(p[0],p[1]);ctx.lineTo(q[0],q[1]);ctx.stroke()});ctx.setLineDash([]);
if(sm&&showNaive){lineP(nv,.03);ctx.strokeStyle='rgba(190,205,235,.85)';ctx.lineWidth=3*dpr;ctx.setLineDash([2*dpr,7*dpr]);ctx.lineCap='round';ctx.stroke();ctx.setLineDash([])}
if(sm){lineP(sm,.04);ctx.shadowColor='#ff9a2e';ctx.shadowBlur=14*dpr;ctx.strokeStyle='#ffb35c';ctx.lineWidth=5*dpr;ctx.lineCap='round';ctx.lineJoin='round';ctx.stroke();ctx.shadowBlur=0}
var items=BL.map(function(b){return boxItem(b.x,b.z,b.w,b.d,b.h,0,b.rgb)});
var dw=wp(DEPOT);items.push(boxItem(dw[0],dw[1],.34,.34,.42,0,[41,121,255],'#2979ff'));
if(sm&&vtot>0){var u=reduce?0:(tk%720)/720,dd=u*vtot,i2=0;while(i2<vp.length-2&&dd>vp[i2+1].c-0)i2++;
var a2=vp[i2],b2=vp[Math.min(i2+1,vp.length-1)],sl=(b2.c-a2.c)||1,f2=Math.max(0,Math.min(1,(dd-a2.c)/sl));
items.push(boxItem(a2.x+(b2.x-a2.x)*f2,a2.z+(b2.z-a2.z)*f2,.3,.17,.15,Math.atan2(b2.z-a2.z,b2.x-a2.x),[235,242,255],'#ff9a2e'))}
items.sort(function(a,b){return b.dep-a.dep});items.forEach(function(it){it.draw()});
var kb=F/12;ctx.textAlign='center';ctx.font='700 '+13*dpr+'px Lexend,system-ui,sans-serif';
var order=sm?stops.slice().sort(function(a,b){return sm.indexOf(a)-sm.indexOf(b)}):stops;
order.forEach(function(sn2,i){var w=wp(sn2),b0=P(w[0],0,w[1]),t0=P(w[0],.62,w[1]),r=12*dpr*t0[3]/kb;
ctx.strokeStyle='#22d3ee';ctx.lineWidth=2*dpr;ctx.beginPath();ctx.moveTo(b0[0],b0[1]);ctx.lineTo(t0[0],t0[1]);ctx.stroke();
ctx.shadowColor='#22d3ee';ctx.shadowBlur=12*dpr;ctx.fillStyle='#22d3ee';ctx.beginPath();ctx.arc(t0[0],t0[1],r,0,7);ctx.fill();ctx.shadowBlur=0;
ctx.fillStyle='#06121f';ctx.fillText(i+1,t0[0],t0[1]+4.5*dpr)});
var dt=P(dw[0],.6,dw[1]);ctx.fillStyle='#e6ecff';ctx.fillText('D',dt[0],dt[1])}
function update(){sm=null;nv=null;
if(stops.length){sm=plan(rw);nv=plan(fw);vp=[];vtot=0;sm.forEach(function(n,i){var w=wp(n);if(i)vtot+=Math.hypot(w[0]-vp[i-1].x,w[1]-vp[i-1].z);vp.push({x:w[0],z:w[1],c:vtot})})}
var S=document.getElementById.bind(document);
if(sm){var cost=pc(sm),ncost=pc(nv),saved=(ncost-cost)*2,dodged=Math.max(0,jc(nv)-jc(sm));
S('mTime').textContent=cost*2+' min';S('mKm').textContent=((sm.length-1)*0.4).toFixed(1)+' km';S('mSaved').textContent=saved+' min';S('mJam').textContent=dodged;
var anyJam=Object.keys(jam).length>0;
S('msg').textContent=saved>0?'The van goes around the jam and saves about '+saved+' min compared with a route that ignores traffic.':anyJam?'The jams are not in the way, so the route stays direct.':'The roads are clear. Add a jam to see the route change.'}
else{['mTime','mKm','mSaved','mJam'].forEach(function(i){S(i).textContent='-'});S('msg').textContent='Tap an intersection on the map to add a delivery stop.'}}
function draw(){update();if(reduce||!vis)frame()}
function loop(){frame();if(vis&&!reduce)loopRaf=requestAnimationFrame(loop)}
function size(){dpr=Math.min(2,window.devicePixelRatio||1);var w=cv.clientWidth||700;W=Math.round(w*dpr);Hh=Math.round(W*.66);cv.width=W;cv.height=Hh;cv.style.height=(Hh/dpr)+'px'}
function pp(e){var r=cv.getBoundingClientRect();return [e.clientX-r.left,e.clientY-r.top]}
function segD(p,a,b){var vx=b[0]-a[0],vy=b[1]-a[1],l=vx*vx+vy*vy||1,u=Math.max(0,Math.min(1,((p[0]-a[0])*vx+(p[1]-a[1])*vy)/l));return Math.hypot(p[0]-(a[0]+vx*u),p[1]-(a[1]+vy*u))}
function pick(p){var bn=-1,bd=16;for(var n=0;n<N;n++){var d=Math.hypot(NP[n][0]-p[0],NP[n][1]-p[1]);if(d<bd){bd=d;bn=n}}
if(bn>-1&&bn!==DEPOT){toggleStop(bn);return}
var be=-1,ed=11;edges.forEach(function(e,i){var d=segD(p,NP[e[0]],NP[e[1]]);if(d<ed){ed=d;be=i}});
if(be>-1){var k=ek(edges[be][0],edges[be][1]);if(jam[k])delete jam[k];else jam[k]=1;draw()}}
cv.addEventListener('pointerdown',function(e){drag=pp(e);moved=0;cv.setPointerCapture&&cv.setPointerCapture(e.pointerId)});
cv.addEventListener('pointermove',function(e){if(!drag)return;var p=pp(e),dx=p[0]-drag[0],dy=p[1]-drag[1];moved+=Math.abs(dx)+Math.abs(dy);yawU-=dx*.008;pit=Math.max(.55,Math.min(1.35,pit+dy*.006));drag=p;if(reduce)frame()});
cv.addEventListener('pointerup',function(e){if(drag&&moved<6)pick(pp(e));drag=null});
cv.addEventListener('pointerleave',function(){drag=null});
window.addEventListener('resize',function(){size();if(reduce)frame()});
if(window.IntersectionObserver)new IntersectionObserver(function(en){var v=en[0].isIntersecting;if(v&&!vis&&!reduce){vis=true;loop()}vis=v},{threshold:0}).observe(cv);
size();if(!reduce)loop();
function toggleStop(n){var i=stops.indexOf(n);if(i>-1)stops.splice(i,1);else if(stops.length<4)stops.push(n);else document.getElementById('msg').textContent='Four stops at most in this demo. Tap a stop to remove it.';draw()}
function addZone(cn){zones.push(cn);edges.forEach(function(e){if(md(e[0],cn)<=2&&md(e[1],cn)<=2)jam[ek(e[0],e[1])]=1})}
document.getElementById('rush').onclick=function(){var cn;do{cn=(1+Math.floor(Math.random()*3))*COLS+1+Math.floor(Math.random()*5)}while(zones.indexOf(cn)>-1);addZone(cn);draw()};
document.getElementById('clrTraffic').onclick=function(){jam={};zones=[];draw()};
document.getElementById('clrStops').onclick=function(){stops=[];draw()};
document.getElementById('addStop').onclick=function(){if(stops.length>=4){stops.shift()}var n;do{n=Math.floor(Math.random()*N)}while(n===DEPOT||stops.indexOf(n)>-1);stops.push(n);draw()};
document.getElementById('naive').onclick=function(){showNaive=!showNaive;this.setAttribute('aria-pressed',showNaive);draw()};
document.getElementById('replay').onclick=draw;
document.getElementById('theme').onclick=function(){var de=document.documentElement;
var cur=de.dataset.theme||(matchMedia('(prefers-color-scheme:light)').matches?'light':'dark');
de.dataset.theme=cur==='dark'?'light':'dark';draw()};
function preset(p){jam={};zones=[];
if(p==='rush'){addZone(17);stops=[9,19,24]}
else if(p==='bridge'){for(var r=0;r<4;r++)jam[ek(r*COLS+2,r*COLS+3)]=1;stops=[10,20,33]}
else if(p==='many'){addZone(9);addZone(19);stops=[8,12,16,26]}
else stops=[9,19,24];
draw();document.getElementById('top').scrollIntoView({behavior:reduce?'auto':'smooth'})}
Array.prototype.forEach.call(document.querySelectorAll('[data-p]'),function(b){b.onclick=function(){preset(b.dataset.p)}});
function calc(){var v=+document.getElementById('cV').value||0,t=+document.getElementById('cT').value||0,m=+document.getElementById('cM').value||0,p=+document.getElementById('cP').value;
document.getElementById('cPv').textContent=p+'%';
document.getElementById('cOut').textContent=Math.round(v*t*m*(p/100)*5/60).toLocaleString('en-US')}
['cV','cT','cM','cP'].forEach(function(i){document.getElementById(i).oninput=calc});calc();
addZone(17);draw();
var gate=document.getElementById('gate');document.body.classList.add('locked');
setTimeout(function(){document.getElementById('fn').focus()},50);
function enter(n){gate.classList.add('hide');document.body.classList.remove('locked');
if(n)document.getElementById('hi').textContent='Welcome, '+n+'.'}
document.getElementById('reg').onsubmit=function(e){e.preventDefault();
var n=document.getElementById('fn').value.trim(),m=document.getElementById('fe').value.trim(),er=document.getElementById('err');
if(!n){er.textContent='Please enter your name.';return}
if(!/^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(m)){er.textContent='Please enter a valid email address.';return}
enter(n)};
document.getElementById('skip').onclick=function(){enter('')};
})();

(function(){
var cv=document.getElementById('globe');if(!cv||!cv.getContext)return;
var ctx=cv.getContext('2d');
var LAND=[
[-168,66,-156,71,-140,70,-125,70,-110,68,-95,70,-85,69,-82,64,-92,59,-94,57,-82,55,-79,52,-78,60,-70,61,-64,58,-60,54,-65,49,-67,45,-70,42,-74,40,-76,35,-81,31,-80,26,-83,29,-89,30,-94,29,-97,26,-97,22,-94,18,-90,21,-87,21,-88,16,-84,15,-83,10,-80,8.5,-83,8,-88,13,-92,14.5,-96,16,-105,20,-106,23,-110,27,-114,31,-117,32.5,-121,35,-124,40,-124,47,-128,51,-135,58,-146,61,-152,59,-160,56,-164,60,-166,64],
[-55,60,-45,60,-20,70,-20,82,-45,83,-65,80,-70,76,-55,70],
[-80,73,-62,67,-65,62,-78,64,-88,70],
[-77,8,-72,12,-62,10,-52,5,-50,0,-44,-2,-35,-6,-38,-13,-40,-20,-48,-26,-53,-34,-58,-38,-62,-41,-65,-45,-68,-52,-70,-55,-74,-50,-74,-40,-71,-30,-70,-18,-76,-14,-81,-5,-80,0,-77,4],
[-9,37,-9,43,-2,43.5,-1,46,-4.5,48,2,51,8,54,10,57.5,8,58,5,59,5,62,10,64,15,68,20,70,28,71,40,68,44,66,55,68,68,69,73,72,80,73,100,77,113,74,130,72,140,72,160,70,170,70,180,68,180,65,172,64,165,61,160,60,163,56,156,51,155,57,143,59,137,54,141,48,135,43,130,42,127,39,129,35,126,35,126,38,122,40,121,37,119,35,122,30,120,26,117,23,110,21,106,20,109,15,109,11,105,8.5,102,12,100,13,99,9,101,3,104,1.5,98,8,98,16,94,17,92,22,88,22,86,20,80,15,80,10,77,8,73,16,72,21,69,22,67,25,61,25,57,26,56,27,52,28,48,30,50,26,51,24,56,25,59,22,55,17,52,16,45,13,43,15,39,21,35,28,34.5,31,36,34,36,36,30,36.5,26,38,23,36.5,21,38.5,19,42,13,45.5,16,41.5,18,40,15.5,38,12,42,8,44,3,43,0,39,-2,37,-5.5,36],
[-17,21,-13,28,-9,32,-6,36,10,37,11,33,20,31,25,32,32,31,34,28,37,22,43,12,51,12,48,4,42,-1,40,-10,40,-15,35,-24,32,-28,28,-33,20,-35,18,-33,15,-26,12,-17,13,-10,9,-1,9,4,4,6,-4,5,-8,4.5,-13,8,-17,14],
[114,-22,122,-18,130,-12,137,-12,141,-12,143,-14,146,-19,153,-26,150,-37,141,-38,135,-34,129,-32,115,-34,113,-26],
[44,-25,47,-25,50,-15,49,-12,44,-17],
[-5,50,1,51,2,53,-2,56,-3,58.5,-6,57,-5,54.5,-3,53,-5,52],
[-10,52,-6,52,-6,55,-10,54],
[130,31,135,34,140,36,142,40,141,42,145,44,140,45,139,40,136,36,131,34],
[95,5,98,4,104,-2,106,-6,101,-3,96,2],
[109,1,117,7,119,1,116,-4,111,-3],
[105,-6,114,-7,114,-8.5,106,-7.5],
[131,-1,141,-3,150,-10,141,-9,137,-5],
[120,18,122,18,126,9,122,7,120,14],
[172,-34,178,-38,175,-41,172,-41],
[167,-46,174,-41,171,-45],
[-24,64,-14,64,-15,66,-22,66],
[-85,22,-80,23,-74,20,-78,20],
[-180,-78,-150,-77,-120,-74,-100,-73,-80,-73,-65,-68,-58,-64,-62,-70,-60,-75,-45,-78,-20,-72,0,-70,20,-69,40,-67,60,-67,70,-68,90,-66,110,-66,130,-66,150,-69,165,-70,170,-72,180,-78,180,-90,-180,-90],
[80,6,82,7.5,80.5,9.5,79.8,8],[120.2,22.5,121.8,25,121.5,22.5],[12.5,38,15.5,38,15,37],[8.2,39,9.7,39,9.7,41,8.3,41],
[-59,47.5,-52.7,47,-53,51.5,-56,51.5],[-74.4,18.5,-68.5,18.5,-69,19.8,-72.5,19.9],[11,78,17,77,25,79,20,80.2],[52,71,58,70.5,69,76.5,60,76.5],
[142,46,143.5,49,143,54,142.2,54],[108.7,19,111,19.5,110.5,20],[144.7,-41,148.3,-41,147.5,-43.5,145.5,-42.5],[119,-5,121,1.3,125,1.5,121,-1,121,-4.5],
[-90,76,-62,82,-75,83,-90,80],[-118,70,-100,69,-102,73,-117,73]];
var WATER=[[47,45,52,47,53,45,54,41,53,37,50,37,49,40,47.5,43],[27.8,41.8,28.5,44,29.7,45.3,31,46.5,33.5,46,35,45,37,44.5,41.5,42,41.5,41.3,38,41,35,42,31,41.2,28.5,41.2],[10,54.3,14,54,19,54.5,21.5,57,23.5,59.5,29.5,60,23,60.4,21.2,61,21.5,63.5,25,65.6,22,65.8,18,62.5,18.5,59.5,16.5,57,15,56,12.7,56,11,55.6]];
window.PATHLY_LAND=LAND;
function inPoly(p,lo,la){var c=false,n=p.length/2;for(var i=0,j=n-1;i<n;j=i++){var xi=p[2*i],yi=p[2*i+1],xj=p[2*j],yj=p[2*j+1];
if((yi>la)!==(yj>la)&&lo<(xj-xi)*(la-yi)/(yj-yi)+xi)c=!c}return c}
function bbx(P){var a=1e9,b=-1e9,c=1e9,d=-1e9;for(var i=0;i<P.length;i+=2){a=Math.min(a,P[i]);b=Math.max(b,P[i]);c=Math.min(c,P[i+1]);d=Math.max(d,P[i+1])}return [a,b,c,d]}
var LB=LAND.map(bbx),WB=WATER.map(bbx);
function inAny(L,B,lo,la){for(var i=0;i<L.length;i++){var b=B[i];if(lo<b[0]||lo>b[1]||la<b[2]||la>b[3])continue;if(inPoly(L[i],lo,la))return true}return false}
function isLand(lo,la){return inAny(LAND,LB,lo,la)&&!inAny(WATER,WB,lo,la)}
var lit=[],M=36000,D=Math.PI/180,G=[];
var PAL=['#1c7f6b','#25927a','#3f8f73','#50a082','#2a6a5c','#33796a','#d49a50','#e4ae68','#8aa0b4','#9db2c4','#e8f2ff','#ffffff','#8b7f86','#9c909a'];
function cls(lo,la){if(la<-60)return 10;if(lo>-75&&lo<-12&&la>59)return 10;if(la>68)return 8;if(lo>74&&lo<102&&la>27&&la<38)return 12;
if((lo>-16&&lo<36&&la>14&&la<31)||(lo>35&&lo<60&&la>14&&la<31)||(lo>88&&lo<112&&la>37&&la<46)||(lo>118&&lo<142&&la>-32&&la<-19)||(lo>15&&lo<25&&la>-28&&la<-18))return 6;
var a=Math.abs(la);return a<23?0:a<45?2:a<66?4:8}
function genLand(){lit=[];G=PAL.map(function(){return []});
for(var i=0;i<M;i++){var y=1-2*(i+.5)/M,r=Math.sqrt(1-y*y),th=i*2.399963,x=Math.cos(th)*r,z=Math.sin(th)*r;
var la=Math.asin(y)/D,lo=Math.atan2(x,z)/D;if(isLand(lo,la)){G[cls(lo,la)+(Math.random()<.5?0:1)].push(x,y,z);if(la>-56&&Math.random()<.1)lit.push([x,y,z,.2+Math.random()*.3])}}}
var CL=[];for(var ci=0;ci<420;ci++){var bd=Math.random(),cla=bd<.3?(Math.random()-.5)*20:bd<.65?(Math.random()<.5?1:-1)*(30+Math.random()*20):(Math.random()<.5?1:-1)*(55+Math.random()*20),clo=Math.random()*360-180;
for(var qq=0;qq<7;qq++){var la2=cla+(Math.random()-.5)*8,lo2=clo+(Math.random()-.5)*14;CL.push(Math.cos(la2*D)*Math.sin(lo2*D)*1.012,Math.sin(la2*D)*1.012,Math.cos(la2*D)*Math.cos(lo2*D)*1.012,.07+Math.random()*.16)}}
var C=[['Mexico City',19.43,-99.13,75.9,184,null,'Mexico'],['Bengaluru',12.97,77.59,74.4,168,null,'India'],['Dublin',53.35,-6.26,72.9,191,null,'Ireland'],['Pune',18.52,73.86,71.1,152,null,'India'],['Bogotá',4.71,-74.07,69.6,153,'31 min 45 s','Colombia'],['Bangkok',13.75,100.5,67.9,115,'22 min 59 s','Thailand'],['Istanbul',41.0,28.98,62,null,null,'Türkiye'],['New Delhi',28.61,77.21,60.2,104,null,'India'],['Jakarta',-6.2,106.85,59.8,null,'26 min 19 s','Indonesia'],['Nairobi',-1.29,36.82,49.6,null,null,'Kenya'],['Cairo',30.04,31.24,40.5,74,null,'Egypt'],
['Davao City',7.07,125.61,66.2,168,null,'Philippines'],['Manila',14.6,120.98,57.0,143,null,'Philippines'],['São Paulo',-23.55,-46.63,58.5,null,null,'Brazil'],['Los Angeles',34.05,-118.24,59.8,83,null,'United States'],['San Francisco',37.77,-122.42,49.7,116,null,'United States'],['New York',40.71,-74.0,48.8,125,null,'United States'],['Chicago',41.88,-87.63,46.1,79,null,'United States'],['Seattle',47.61,-122.33,44.9,69,null,'United States'],['Miami',25.76,-80.19,46.8,72,null,'United States'],['London',51.51,-0.13,51.6,null,null,'United Kingdom'],['Melbourne',-37.81,144.96,52.9,null,null,'Australia'],['Adelaide',-34.93,138.6,55.1,109,null,'Australia'],['Sydney',-33.87,151.21,43.7,null,null,'Australia']];
C.sort(function(a,b){return b[3]-a[3]});window.PATHLY_CITIES=C;
function genClusters(){C.forEach(function(c){var n=0,tr=0;while(n<70&&tr<300){tr++;var lo=c[2]+(Math.random()+Math.random()+Math.random()-1.5)*8,la=c[1]+(Math.random()+Math.random()+Math.random()-1.5)*5;
if(isLand(lo,la)){lit.push([Math.cos(la*D)*Math.sin(lo*D),Math.sin(la*D),Math.cos(la*D)*Math.cos(lo*D),.6+Math.random()*.4]);n++}}})}
function rebuild(){genLand();genClusters()}
rebuild();

var yaw=-99*D,pit=18*D,sel=-1,hov=-1,drag=null,moved=0,tw=null,vis=true,t=0,col={};
var reduce=matchMedia('(prefers-reduced-motion:reduce)').matches;
function colors(){col={'--ink':'#e6ecff'}}
function xyz(la,lo){return [Math.cos(la*D)*Math.sin(lo*D),Math.sin(la*D),Math.cos(la*D)*Math.cos(lo*D)]}
function rot(p,s){var a=Math.cos(yaw),b=Math.sin(yaw),x1=p[0]*a-p[2]*b,z1=p[0]*b+p[2]*a,c=Math.cos(pit),d=Math.sin(pit);
return [x1,p[1]*c-z1*d,p[1]*d+z1*c]}
var W=0,H=0,R=0,dpr=1,hit=[];
var spr=document.createElement('canvas');spr.width=spr.height=32;(function(){var g=spr.getContext('2d'),r=g.createRadialGradient(16,16,0,16,16,16);r.addColorStop(0,'rgba(255,255,255,1)');r.addColorStop(1,'rgba(255,255,255,0)');g.fillStyle=r;g.fillRect(0,0,32,32)})();
function size(){dpr=Math.min(2,window.devicePixelRatio||1);var w=cv.clientWidth||400;W=Math.round(w*dpr);H=W;cv.width=W;cv.height=H;R=W*0.40}
function lvlCol(l){return 'hsl('+Math.max(0,Math.min(50,(78-l)*1.4))+',95%,55%)'}
function frame(){
if(++t%60===1)colors();
if(tw){var k0=Math.min(1,(t-tw.t0)/45),e0=1-Math.pow(1-k0,3);yaw=tw.y0+tw.dy*e0;pit=tw.p0+tw.dp*e0;if(k0>=1)tw=null}
else if(!drag&&!reduce&&hov<0)yaw+=0.0025;
ctx.clearRect(0,0,W,H);var cx=W/2,cy=H/2;
var ag=ctx.createRadialGradient(cx,cy,R*.98,cx,cy,R*1.16);ag.addColorStop(0,'rgba(110,185,255,.55)');ag.addColorStop(1,'rgba(110,185,255,0)');
ctx.fillStyle=ag;ctx.beginPath();ctx.arc(cx,cy,R*1.16,0,7);ctx.fill();
ctx.save();ctx.beginPath();ctx.arc(cx,cy,R,0,7);ctx.clip();
var og=ctx.createRadialGradient(cx-R*.35,cy-R*.35,R*.05,cx,cy,R);og.addColorStop(0,'#2a6fd6');og.addColorStop(.55,'#123f9a');og.addColorStop(1,'#050f34');
ctx.fillStyle=og;ctx.fillRect(cx-R,cy-R,2*R,2*R);
var cw=Math.cos(yaw),sw=Math.sin(yaw),cp=Math.cos(pit),sp=Math.sin(pit),sz=R*.023;
for(var k=0;k<G.length;k++){var arr=G[k];ctx.fillStyle=PAL[k];
for(var i=0;i<arr.length;i+=3){var x=arr[i],y=arr[i+1],z=arr[i+2],x1=x*cw-z*sw,z1=x*sw+z*cw;if(y*sp+z1*cp<0.01)continue;ctx.fillRect(cx+x1*R-sz/2,cy-(y*cp-z1*sp)*R-sz/2,sz,sz)}}
var yc=yaw+t*0.0006,cc=Math.cos(yc),sc=Math.sin(yc),cz=R*.04;
for(var j=0;j<CL.length;j+=4){var x=CL[j],y=CL[j+1],z=CL[j+2],x1=x*cc-z*sc,z1=x*sc+z*cc,z2=y*sp+z1*cp;if(z2<0.02)continue;ctx.globalAlpha=Math.min(1,CL[j+3]*1.9*(.4+.6*z2));ctx.drawImage(spr,cx+x1*R-cz,cy-(y*cp-z1*sp)*R-cz,cz*2,cz*2)}
ctx.globalAlpha=1;
var sh=ctx.createRadialGradient(cx-R*.55,cy-R*.4,R*.35,cx-R*.1,cy-R*.05,R*1.5);sh.addColorStop(0,'rgba(0,10,40,0)');sh.addColorStop(.55,'rgba(0,10,40,.06)');sh.addColorStop(1,'rgba(0,6,24,.8)');
ctx.fillStyle=sh;ctx.fillRect(cx-R,cy-R,2*R,2*R);
var s2=ctx.createRadialGradient(cx-R*.4,cy-R*.45,0,cx-R*.4,cy-R*.45,R*.35);s2.addColorStop(0,'rgba(255,255,255,.16)');s2.addColorStop(1,'rgba(255,255,255,0)');ctx.fillStyle=s2;ctx.fillRect(cx-R,cy-R,2*R,2*R);
var lb=ctx.createRadialGradient(cx,cy,R*.78,cx,cy,R);lb.addColorStop(0,'rgba(120,190,255,0)');lb.addColorStop(1,'rgba(120,190,255,.34)');ctx.fillStyle=lb;ctx.fillRect(cx-R,cy-R,2*R,2*R);
ctx.restore();
ctx.save();ctx.globalCompositeOperation='lighter';ctx.fillStyle='#ffa23a';
for(var m=0;m<lit.length;m++){var d=lit[m],x1=d[0]*cw-d[2]*sw,z1=d[0]*sw+d[2]*cw,z2=d[1]*sp+z1*cp;if(z2<0.02)continue;var y2=d[1]*cp-z1*sp,sd=-.5*x1+.4*y2+.7*z2;
ctx.globalAlpha=(.18+d[3]*.75)*(sd<.25?1:.3)*(.4+.6*z2);var zz=(1.1+d[3]*1.7)*dpr;ctx.fillRect(cx+x1*R-zz/2,cy-y2*R-zz/2,zz,zz)}
ctx.restore();
ctx.strokeStyle='rgba(150,205,255,.35)';ctx.lineWidth=1.4*dpr;ctx.beginPath();ctx.arc(cx,cy,R,0,7);ctx.stroke();
hit=[];var items=[];
C.forEach(function(c,i){var p=xyz(c[1],c[2]),q=rot(p);if(q[2]<-0.02)return;items.push([i,q,p])});
items.sort(function(a,b){return a[1][2]-b[1][2]});
items.forEach(function(it){var i=it[0],c=C[i],p=it[2],q=it[1],h=0.04+Math.max(0,c[3]-30)/50*0.22,q2=rot([p[0]*(1+h),p[1]*(1+h),p[2]*(1+h)]);
var bx=cx+q[0]*R,by=cy-q[1]*R,tx=cx+q2[0]*R,ty=cy-q2[1]*R,cl=lvlCol(c[3]),on=i===sel||i===hov,pulse=(Math.sin(t*0.07+i)+1)/2;
ctx.globalAlpha=.3+.3*pulse;ctx.fillStyle=cl;ctx.beginPath();ctx.arc(bx,by,(6+c[3]/9)*dpr*(0.5+0.5*q[2]),0,7);ctx.fill();
ctx.globalAlpha=1;ctx.shadowColor=cl;ctx.shadowBlur=10*dpr;ctx.strokeStyle=cl;ctx.lineWidth=(on?4:2.8)*dpr;ctx.lineCap='round';ctx.beginPath();ctx.moveTo(bx,by);ctx.lineTo(tx,ty);ctx.stroke();
ctx.fillStyle=cl;ctx.beginPath();ctx.arc(tx,ty,(on?6:4)*dpr,0,7);ctx.fill();ctx.shadowBlur=0;
if(on){ctx.strokeStyle=col['--ink'];ctx.lineWidth=1.5*dpr;ctx.beginPath();ctx.arc(tx,ty,(8+2*pulse)*dpr,0,7);ctx.stroke();
ctx.shadowColor='#000';ctx.shadowBlur=6*dpr;ctx.fillStyle=col['--ink'];ctx.font='600 '+13*dpr+'px Lexend,system-ui,sans-serif';ctx.textAlign='center';ctx.fillText(c[0],tx,ty-14*dpr);ctx.shadowBlur=0}
if(q[2]>0.1)hit.push([i,tx/dpr,ty/dpr])});
if(vis&&!reduce)requestAnimationFrame(frame)}
function redraw(){if(reduce||!vis)frame()}
function select(i,go,quiet){sel=i;var c=C[i];document.getElementById('wName').textContent=c[0];document.getElementById('wTag').textContent=c[6]+(c[4]?' · '+c[4]+' hours lost in rush hour per driver (2025)':'');
document.getElementById('wBar').style.width=Math.min(100,c[3]/80*100)+'%';document.getElementById('wLvl').textContent='Congestion level '+c[3]+'% in 2025'+(c[5]?' · a 10 km drive takes '+c[5]:'');
Array.prototype.forEach.call(document.querySelectorAll('#wList button'),function(b,k){b.setAttribute('aria-pressed',k===i)});
if(go){var dy=((c[2]*D-yaw+Math.PI*3)%(Math.PI*2))-Math.PI;tw={t0:t,y0:yaw,dy:dy,p0:pit,dp:Math.max(-1.1,Math.min(1.1,c[1]*D*0.8))-pit}}redraw();if(!quiet&&window.PATHLY_ON)window.PATHLY_ON(i)}
window.PATHLY_PICK=function(i){select(i,true,true)};

function pt(e){var r=cv.getBoundingClientRect();return [e.clientX-r.left,e.clientY-r.top]}
function near(p){var b=-1,bd=22;hit.forEach(function(h){var d=Math.hypot(h[1]-p[0],h[2]-p[1]);if(d<bd){bd=d;b=h[0]}});return b}
cv.addEventListener('pointerdown',function(e){drag=pt(e);moved=0;tw=null;cv.setPointerCapture&&cv.setPointerCapture(e.pointerId)});
cv.addEventListener('pointermove',function(e){var p=pt(e);
if(drag){var dx=p[0]-drag[0],dy=p[1]-drag[1];moved+=Math.abs(dx)+Math.abs(dy);yaw-=dx*0.007;pit=Math.max(-1.2,Math.min(1.2,pit+dy*0.007));drag=p;redraw()}
else{var n=near(p);if(n!==hov){hov=n;cv.style.cursor=n>-1?'pointer':'grab';redraw()}}});
cv.addEventListener('pointerup',function(e){if(drag&&moved<6){var n=near(pt(e));if(n>-1)select(n,true)}drag=null});
cv.addEventListener('pointerleave',function(){hov=-1;drag=null});
window.addEventListener('resize',function(){size();redraw()});
document.getElementById('theme').addEventListener('click',function(){setTimeout(function(){colors();redraw()},0)});
if(window.IntersectionObserver)new IntersectionObserver(function(en){var v=en[0].isIntersecting;if(v&&!vis&&!reduce){vis=true;requestAnimationFrame(frame)}vis=v;},{threshold:0}).observe(cv);
function useGeo(g){try{var rings=[];(g.features||[]).forEach(function(f){var ge=f.geometry;if(!ge)return;
var pl=ge.type==='Polygon'?[ge.coordinates]:ge.type==='MultiPolygon'?ge.coordinates:[];
pl.forEach(function(p){var r=p[0];if(r&&r.length>3){var fl=[];for(var i=0;i<r.length;i++)fl.push(r[i][0],r[i][1]);rings.push(fl)}})});
if(rings.length<60)return false;LAND=rings;WATER=[];LB=LAND.map(bbx);WB=[];rebuild();redraw();return true}catch(e){return false}}
(function(){var src='https://cdn.jsdelivr.net/npm/@amcharts/amcharts4-geodata@4.1.30/dist/script/worldLow.js';
try{var sc=document.createElement('script');sc.src=src;sc.async=true;sc.onload=function(){useGeo(window.am4geodata_worldLow)};sc.onerror=function(){};
(document.head||document.body).appendChild(sc)}catch(e){}})();
colors();size();select(0,false);frame();
})();

(function(){
var D=window.PATHLY_CITIES||[];if(!D.length)return;
var reduce=matchMedia('(prefers-reduced-motion:reduce)').matches;
function hc(l){return 'hsl('+Math.max(0,Math.min(50,(78-l)*1.4))+',95%,58%)'}
var L=document.getElementById('cList'),TB=document.getElementById('cRows');
D.forEach(function(c,i){var b=document.createElement('button');b.type='button';b.setAttribute('aria-pressed','false');
b.innerHTML='<i style="background:'+hc(c[3])+'"></i>'+c[0]+'<em>'+c[3]+'%</em>';b.onclick=function(){select(i)};L.appendChild(b)});
TB.innerHTML=D.map(function(c,i){return '<tr data-i="'+i+'"><td>'+c[0]+'</td><td>'+c[3]+'%</td><td>'+(c[4]?c[4]+' h':'-')+'</td></tr>'}).join('');
TB.onclick=function(e){var tr=e.target.closest&&e.target.closest('tr');if(tr)select(+tr.dataset.i)};
function mark(i){Array.prototype.forEach.call(L.children,function(b,k){b.setAttribute('aria-pressed',k===i)});
Array.prototype.forEach.call(TB.children,function(tr,k){tr.setAttribute('aria-selected',k===i)})}
function select(i){mark(i);if(window.PATHLY_PICK)window.PATHLY_PICK(i)}
window.PATHLY_ON=mark;
var B=D.filter(function(c){return c[4]}).sort(function(a,b){return b[4]-a[4]}),bc=document.getElementById('cbars'),bx=bc.getContext('2d'),gr=1;
function bars(){var n=B.length,h=n*15+8,w=bc.clientWidth||300,d=Math.min(2,window.devicePixelRatio||1);bc.style.height=h+'px';bc.width=w*d;bc.height=h*d;bx.setTransform(d,0,0,d,0,0);bx.clearRect(0,0,w,h);
var rh=(h-6)/n,left=96,right=40;
B.forEach(function(c,i){var y=i*rh+4,bw=(w-left-right)*(c[4]/200)*gr;
bx.fillStyle='#8392b8';bx.font='10.5px Lexend,sans-serif';bx.textAlign='left';bx.fillText(c[0],0,y+rh/2+1);
var g=bx.createLinearGradient(left,0,left+bw+1,0);g.addColorStop(0,'#a8530a');g.addColorStop(1,'#ffb55c');bx.fillStyle=g;bx.fillRect(left,y,bw,rh-6);
bx.fillStyle='#e6ecff';bx.fillText(c[4]+' h',left+bw+5,y+rh/2+1)})}
function run(){var k=document.querySelectorAll('.kpis b'),T=[];Array.prototype.forEach.call(k,function(el){T.push(+el.dataset.k)});
var t0=null;function step(ts){if(t0===null)t0=ts;var p=reduce?1:Math.min(1,(ts-t0)/1400),e=1-Math.pow(1-p,3);
Array.prototype.forEach.call(k,function(el,i){var d=+el.dataset.d||0,v=T[i]*e;el.textContent=(d?v.toFixed(d):Math.round(v).toLocaleString('en-US'))+(el.dataset.s||'')});
gr=e;bars();var gv=75.9*e;document.getElementById('gArc').setAttribute('stroke-dashoffset',326.7*(1-gv/100));document.getElementById('gTxt').textContent=gv.toFixed(1)+'%';
if(p<1)requestAnimationFrame(step)}
requestAnimationFrame(step)}
window.addEventListener('resize',bars);
var started=false;function go(){if(started)return;started=true;run()}
var kp=document.querySelector('.kpis');
if(window.IntersectionObserver&&kp)new IntersectionObserver(function(en){if(en[0].isIntersecting)go()},{threshold:.1}).observe(kp);else go();
mark(0);bars();
})();
