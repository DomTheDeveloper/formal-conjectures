# Counterexample to WOWII Graph Conjecture 109

Construct three disjoint seven-vertex gadgets. In gadget `i`, vertices `a_i,b_i,c_i` span a triangle, two private leaves are attached to `a_i`, and two private leaves are attached to `b_i`. Add the three cross-edges

`a_0 a_1`, `b_0 a_2`, and `b_1 b_2`.

The resulting graph `G` is connected and has 21 vertices.

## Independence number

In each gadget, `c_i` together with the four leaves is an independent set of size five. Their union is unaffected by the cross-edges, so `alpha(G)>=15`. No independent set contains more than five vertices from any gadget, hence `alpha(G)=15`.

## Largest induced bipartite subgraph

Every gadget contains a triangle, so an induced bipartite subgraph must omit at least one vertex from each gadget. Hence `b(G)<=18`. Delete `c_0,c_1,c_2`. The remaining graph is bipartite: color `a_0,a_2,b_1` on one side, `b_0,a_1,b_2` on the other, and color every private leaf opposite its attachment vertex. Thus `b(G)=18`.

## Havel--Hakimi residue

The degree sequence is

`[5,5,5,5,5,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1]`.

Successive Havel--Hakimi reductions give

```
[4,4,4,4,4,2,2,2,1^12]
[3,3,3,3,2,2,2,1^12]
[2,2,2,2,2,2,1^12]
[2,2,2,1^14]
[1^16]
[1^14,0]
[1^12,0^2]
[1^10,0^3]
[1^8,0^4]
[1^6,0^5]
[1^4,0^6]
[1^2,0^7]
[0^8].
```

Therefore `residue(G)=8`.

The conjectured upper bound is

`floor((residue(G)+2*b(G))/3) = floor((8+36)/3)=14`,

but `alpha(G)=15`. Thus Conjecture 109 is false.
