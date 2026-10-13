"""Independent finite reconstruction from Pyle Definitions 4–6.
Does not import the author's Python, lists, graph, or compiled Lean objects.
Frozen Lean lists are compared only after all model sets are constructed.
"""
from itertools import product,permutations,combinations_with_replacement
from collections import Counter,deque
from pathlib import Path
import re,json,hashlib
root=Path(__file__).resolve().parent;src=root/'sources'
# Recognize the predicate on an unordered multiset, checking every ordering.
def literal_multiset(ms):
 for p in set(permutations(ms)):
  ds=[(p[i+1]-p[i])%12 for i in range(3)]
  if ds.count(0)==1 and all(d in (0,3,4) for d in ds):return True
  if len(set(p))==4 and all(d in (3,4) for d in ds):return True
 return False
valid_multisets={x for x in combinations_with_replacement(range(12),4) if literal_multiset(x)}
Q={c for c in product(range(12),repeat=4) if tuple(sorted(c)) in valid_multisets}
# Separate forward construction from root, stacking increments, transposition,
# and permutations; equality prevents a one-sided chord-recognizer mistake.
T=set()
for ds in product((0,3,4),repeat=3):
 if not (ds.count(0)==1 or ds.count(0)==0):continue
 shape=(0,ds[0],sum(ds[:2])%12,sum(ds)%12)
 if ds.count(0)==0 and len(set(shape))!=4:continue
 for rootpc in range(12):
  for p in permutations(shape):T.add(tuple((rootpc+x)%12 for x in p))
assert Q==T

def step(c,v):return ((c[0]-1)%12,)+tuple((c[i]+(i==v))%12 for i in range(1,4))
def typ(c):return tuple(sorted((x-c[0])%12 for x in c[1:]))
I=[{step(c,v) for c in Q} for v in (1,2,3)];U=set.union(*I);A=Q&U
nodes={typ(c) for c in Q};edges={q:set() for q in nodes}
for c in Q:
 for v in (1,2,3):
  d=step(c,v)
  if d in Q:edges[typ(c)].add(typ(d))
# Quotient local equality is checked from every actual representative.
for c in Q:
 assert {typ(step(c,v)) for v in (1,2,3) if step(c,v) in Q}==edges[typ(c)]
# Independently use relative coordinates: +2 in chosen coordinate, +1 in others.
for q in nodes:
 direct={tuple(sorted((q[i]+1+(i==v))%12 for i in range(3))) for v in range(3)}
 assert edges[q]==direct&nodes

def reach(q):
 r={q};todo=[q]
 while todo:
  for s in edges[todo.pop()]-r:r.add(s);todo.append(s)
 return r
closures={q:reach(q) for q in nodes}
nonterminal_max=max(sum(bool(edges[x]) for x in r) for r in closures.values())
assert nonterminal_max==7
# Greatest fixed point of vertices supporting an infinite continuation.
viable=set(nodes)
while True:
 new={q for q in viable if edges[q]&viable}
 if new==viable:break
 viable=new
# Exhaustive visited-set search counts arbitrary walks, not just simple paths.
number={q:i for i,q in enumerate(sorted(nodes))}
def exact_walk_max(allowed):
 seen={(q,1<<number[q]) for q in allowed};todo=deque(seen);maxn=0
 while todo:
  q,mask=todo.popleft();maxn=max(maxn,mask.bit_count())
  for d in edges[q]&allowed:
   s=(d,mask|(1<<number[d]))
   if s not in seen:seen.add(s);todo.append(s)
 return maxn,len(seen)
finite_max,finite_states=exact_walk_max(nodes)
infinite_max,infinite_states=exact_walk_max(viable)
assert (finite_max,infinite_max)==(8,7)
# A theorem about approachability-restricted starts is NOT exported by the
# frozen Lean roots; these checks only establish the witness scope restriction.
indegree={q:sum(q in edges[p] for p in nodes) for q in nodes}
assert all((c in A)==bool(indegree[typ(c)]) for c in Q)

# Now compare independent data with the frozen Lean certificate fixtures.
shape_rx=r'⟨(\d+),(\d+),(\d+)⟩';chord_rx=r'⟨(\d+),(\d+),(\d+),(\d+)⟩'
node_source=(src/'NodeJoin.lean').read_text().split('def checkedNodeList : List Shape :=',1)[1].split('\n\ntheorem',1)[0]
lean_nodes=[tuple(map(int,x)) for x in re.findall(shape_rx,node_source)]
assert len(lean_nodes)==len(set(lean_nodes))==55 and set(lean_nodes)==nodes
checked_edges=set()
for n in range(7):
 s=(src/f'EdgeSlice{n}.lean').read_text()
 for match in re.finditer(r'theorem successor_\d+ : successors (⟨\d+,\d+,\d+⟩) = (\[.*?\]) := by decide',s,re.S):
  q=tuple(map(int,re.fullmatch(shape_rx,match[1]).groups()))
  ds={tuple(map(int,x)) for x in re.findall(shape_rx,match[2])}
  assert edges[q]==ds
  assert q not in checked_edges
  checked_edges.add(q)
assert checked_edges==nodes
# Direct fixed literals, independent from arbitrary-word theorem proofs.
s=(src/'Pilot.lean').read_text().split('def witness : List Chord :=',1)[1].split('\n\ntheorem',1)[0]
finite=[tuple(map(int,x)) for x in re.findall(chord_rx,s)]
period_text=(src/'PeriodicWitness.lean').read_text().split('def periodStates : Array Chord := #[',1)[1].split('\n]',1)[0]
period=[tuple(map(int,x)) for x in re.findall(chord_rx,period_text)]
assert len(finite)==8 and all(c in Q for c in finite)
assert all(any(step(c,v)==d for v in (1,2,3)) for c,d in zip(finite,finite[1:]))
assert len({typ(c) for c in finite})==8
assert len(period)==len(set(period))==36 and all(c in Q for c in period)
assert all(any(step(c,v)==d for v in (1,2,3)) for c,d in zip(period,period[1:]+period[:1]))
assert any(step(finite[0],v)==period[0] for v in (1,2,3))
assert len({typ(c) for c in [finite[0]]+period})==7
assert finite[0] not in U and indegree[typ(finite[0])]==0
image_tenor=[sum(c[0]==0 and c[1]==x for c in U) for x in range(12)]
approachable_tenor=[sum(c[0]==0 and c[1]==x for c in A) for x in range(12)]
assert image_tenor==[16,34,24,16,65,68,61,52,52,67,71,44]
assert approachable_tenor==[12,6,6,12,31,22,13,16,21,35,6,6]
assert (len(Q),len(U),len(A),len(nodes),sum(map(len,edges.values())))==(3240,6840,2232,55,49)
result={'status':'passed','ordered_chords':len(Q),'all_actual_move_endpoints':len(U),'valid_approachable_endpoints':len(A),'invalid_endpoints':len(U-Q),'valid_unapproachable_chords':len(Q-U),'types':len(nodes),'directed_edges':sum(map(len,edges.values())),'frozen_successor_equations_compared':len(checked_edges),'individual_voice_images':[len(x) for x in I],'pair_intersections':[len(I[i]&I[j]) for i,j in ((0,1),(0,2),(1,2))],'triple_intersection':len(set.intersection(*I)),'image_predecessor_voice_multiplicity':dict(sorted(Counter(sum(c in i for i in I) for c in U).items())),'image_tenor_counts':image_tenor,'approachable_tenor_counts':approachable_tenor,'max_nonterminal_reachable_types':nonterminal_max,'max_distinct_types_finite_walk':finite_max,'max_distinct_types_infinite_walk':infinite_max,'finite_walk_visited_states':finite_states,'infinite_walk_visited_states':infinite_states,'witness_start':finite[0],'witness_start_approachable':False,'period_ordered_chords':len(period),'all_representatives_local_quotient_checked':len(Q),'source_model':'independent literal predicate plus separate template generation','lean_objects_loaded':0}
(root/'independent_fixture_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
