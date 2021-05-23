% 0..n are nat numbers
nat(0..n).

% T has some (unique) nt positive number of vertices
{nt(1..n)} = 1.


% 1..nt are colors (i.e. tree nodes)
color(1..X) :- nt(X).

% 0..nt-1 are depths and heights
depth(0..X) :- nt(X+1).

% 1 is always (the unique) root and has depth 0
root(1).
:- root(X), X != 1.
hasDepth(1, 0).

% each node in the tree (except the root) has a (unique) parent
{parent(Y, X) : color(Y), Y<X} = 1 :- color(X), X != 1.
:- root(X), parent(Y, X).

% root is parent of something
1 {parent(1, X) : color(X)}.

% adjacent colors are not subset of eachother
%1 {hasColor(N, X) : node(N), not hasColor(N, Y)} :- parent(Y, X).
%1 {hasColor(N, Y) : node(N), not hasColor(N, X)} :- parent(Y, X).

% no self-loops
:- color(X), parent(X, X).

% parent relation gives a depth
hasDepth(X, Z+1) :- parent(Y, X),
                    depth(Z), depth(Z+1), hasDepth(Y, Z).

% each color has a unique and constrained depth
{hasDepth(X, D) : depth(D)} = 1 :- color(X).
:- color(X), not root(X), hasDepth(X, 0).
:- color(X), color(Y), parent(Y, X), hasDepth(Y, Z), nt(Z+1).

% symmetry break: depth is non-decreasing w.r.t index
:- hasDepth(X, DX), hasDepth(Y, DY), X<Y, DX>DY.





% 1..n are graph nodes
node(1..n).

%edge(X, Y) :- node(X), node(Y), X < Y.

% each node has some colors
1 {hasColor(X, C) : color(C)} :- node(X).

% if I want a color in T, than it has to be used
1 {hasColor(X, C) : node(X)} :- color(C).

% TD 1: already satisfied because each node has a color

% TD 2: if edge(x, y),  then x and y share a color
agree(X, Y) :- hasColor(X, C), hasColor(Y, C), X < Y.
:- edge(X, Y), not agree(X, Y).

% TD 3: if x has colors r and t, then it has color s for each s in path(r->t)
hasColor(X, S) :- R != S, R != T, S != T,
                    hasColor(X, R), hasColor(X, T), inPath(R, S, T).


% lca for find inPath fast
ancestor(Y, X) :- parent(Y, X).
ancestor(Z, X) :- parent(Y, X), ancestor(Z, Y).

lca(X, X, X) :- color(X).
lca(X, Y, Z) :- lca(Y, X, Z).
lca(X, Y, Z) :- lca(X, W, Z), parent(W, Y), not ancestor(Y, X), X != Y, Z <= W, Z <= X, Z <= Y.

inPath(X, X, X) :- color(X).
inPath(X, Y, Z) :- inPath(Z, Y, X).
inPath(X, Y, Z) :- ancestor(Z, Y), ancestor(Y, X), Z < Y, Y < X.
inPath(X, Y, Z) :- lca(X, Z, W), inPath(Z, Y, W), W <= X, W <= Z.


% cardinality of chi
size(C, S) :- color(C), S = #count {X : node(X), hasColor(X, C)}.

% tree width
treeWidth(X) :- X+1 = #max {S,C : size(C, S)}.

#minimize {X : treeWidth(X)}.

%#show parent/2.
%#show lca/3.
%#show inPath/3.

#show size/2.