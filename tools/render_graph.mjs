import { instance } from '@viz-js/viz';
import fs from 'node:fs';
import path from 'node:path';
import { Script } from 'node:vm';
const root=path.resolve(process.argv[2] || '.');
const data=JSON.parse(fs.readFileSync(path.join(root,'audit/inventory.json'),'utf8'));
const coverage=JSON.parse(fs.readFileSync(path.join(root,'audit/coverage.json'),'utf8'));
const coverageById=Object.fromEntries(coverage.results.map(r=>[r.paper_id,r]));
for(const n of data.nodes)n.coverage=coverageById[n.id]||null;
const viz=await instance();
const esc=s=>JSON.stringify(s);
let dot='digraph G { graph [rankdir=TB, bgcolor="white", pad=0.4, nodesep=0.28, ranksep=0.65, splines=polyline, label="GD stepsize composition: mathematical dependencies\nArrows: prerequisite → conclusion.", labelloc=t, fontsize=22, fontname="Arial"];\n node [shape=box, style="rounded,filled", fontname="Arial", fontsize=11, margin="0.16,0.11", color="#bcc9d5", fillcolor="#edf3f8"]; edge [color="#9baab9", arrowsize=0.5, penwidth=0.7];\n';
for(const n of data.nodes){
 const color=n.coverage ? ({verified_scalar_model:'#d8f0e3',partial:'#ffe5bb',open:'#f6d9dd'}[n.coverage.status]) : n.kind==='External'?'#fff0d6':['Definition','Bridge'].includes(n.kind)?'#f0f1f3':n.kind==='Certificate'?'#eee6fc':'#e8f3f2';
 dot+=`${esc(n.id)} [id=${esc('node-'+n.id)},label=${esc(n.kind+' '+n.id+'\n'+n.title)},fillcolor=${esc(color)},tooltip=${esc('Pages '+n.pages.join(', '))}];\n`;
}
for(const n of data.nodes)for(const d of n.depends_on)dot+=`${esc(d)} -> ${esc(n.id)};\n`;
dot+='}';
fs.writeFileSync(path.join(root,'graphs/manuscript_dag.dot'),dot);
let svg=viz.renderString(dot,{format:'svg'}).replace(/<a\s[^>]*>/g,'').replace(/<\/a>/g,'');
fs.writeFileSync(path.join(root,'graphs/manuscript_dag.svg'),svg);
const embedded=JSON.stringify(data).replaceAll('<','\\u003c');
let html=`<!doctype html><html lang="zh"><meta charset="utf-8"><title>GD theorem DAG</title>
<style>body{margin:0;font:15px/1.55 system-ui;color:#243647;background:#f6f8fa}header{padding:20px 28px;border-bottom:1px solid #ddd;background:white}h1{font-size:24px;margin:0 0 7px}main{display:grid;grid-template-columns:minmax(0,1fr) 410px;height:calc(100vh - 130px)}#graph{overflow:auto;background:white;padding:18px}#graph svg{width:100%;height:auto;min-width:1100px}aside{overflow:auto;padding:24px;border-left:1px solid #ddd}pre{white-space:pre-wrap;font-size:12px;background:white;padding:16px}.node{cursor:pointer}.node:hover polygon,.node:hover path{stroke:#17675e;stroke-width:3}.selected polygon,.selected path{stroke:#bd4a24!important;stroke-width:3!important}select{font:inherit;padding:6px;margin-top:8px}small{color:#65758a}li{margin:4px 0}button{cursor:pointer;color:#17675e;border:0;background:none;font:inherit;text-align:left}</style>
<header><h1>数学结论依赖图</h1><div>${coverage.results.length} 个编号结论 · ${data.nodes.length} 个节点 · ${data.nodes.reduce((s,n)=>s+n.depends_on.length,0)} 条依赖。点击节点查看陈述、Lean 声明和前置结果。</div><small>编号结论：绿色表示标量／组合陈述已验证，橙色表示部分完成，红色表示未完成。其他节点表示定义、辅助结果、证书或外部接口，不计入编号结论覆盖率。</small></header>
<main><div id="graph">${svg.replace(/<\?xml[^>]*>/,'').replace(/<!DOCTYPE[\s\S]*?>/,'')}</div><aside><label>选择结论 <select id="pick"></select></label><div id="details"></div></aside></main>
<script>const data=${embedded};const byId=Object.fromEntries(data.nodes.map(n=>[n.id,n]));const pick=document.getElementById('pick');for(const n of data.nodes){let o=document.createElement('option');o.value=n.id;o.textContent=n.kind+' '+n.id+' — '+n.title;pick.append(o)}function show(id){const n=byId[id];pick.value=id;document.querySelectorAll('.selected').forEach(x=>x.classList.remove('selected'));document.getElementById('node-'+id)?.classList.add('selected');const box=document.getElementById('details');box.replaceChildren();let h=document.createElement('h2');h.textContent=n.kind+' '+id;box.append(h);let p=document.createElement('p');p.textContent=n.title+' · PDF 页 '+n.pages.join(', ');box.append(p);if(n.coverage){let s=document.createElement('p');s.textContent='Lean: '+n.coverage.status+' — '+n.coverage.scope_note;box.append(s);let c=document.createElement('pre');c.textContent=(n.coverage.proof_declarations||[]).join('\\n')+'\\nTarget: '+(n.coverage.target_definition||'见报告');box.append(c)}for(const [label,ids] of [['前置结果',n.depends_on],['直接支持',data.nodes.filter(x=>x.depends_on.includes(id)).map(x=>x.id)]]){let h=document.createElement('h3');h.textContent=label;box.append(h);let ul=document.createElement('ul');for(const k of ids){let li=document.createElement('li'),b=document.createElement('button');b.textContent=k+' '+byId[k].title;b.onclick=()=>show(k);li.append(b);ul.append(li)}box.append(ul)}if(n.statement_excerpt){let pre=document.createElement('pre');pre.textContent=n.statement_excerpt;box.append(pre)}}pick.onchange=()=>show(pick.value);for(const n of data.nodes)document.getElementById('node-'+n.id)?.addEventListener('click',()=>show(n.id));show('3.1');</script></html>`;
const clientScript=html.match(/<script>([\s\S]*?)<\/script>/)?.[1];
if(!clientScript)throw new Error('Interactive graph script is missing.');
new Script(clientScript,{filename:'graphs/manuscript_dag.html'});
fs.writeFileSync(path.join(root,'graphs/manuscript_dag.html'),html);
console.log(JSON.stringify({svg:'graphs/manuscript_dag.svg',interactive:'graphs/manuscript_dag.html',nodes:data.nodes.length}));
