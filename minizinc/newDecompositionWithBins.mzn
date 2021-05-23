include "alldifferent_except_0.mzn";

int: N;
array[1..N, 1..N] of 0..1: graph; % input graph

var 1..N: n; % size of tree T

array[1..N] of var 0..N: parent; % parent[x] of each node x in T (0 if x is root, i.e. x=1)
array[1..N] of var 0..N-1: depth; % depth[x] of each node x in T
array[1..N, 1..N] of var 0..1: ancestor; % ancestor[y, x] iff y is ancestor of x
array[1..N, 1..N] of var 0..N: lca; % collects lca of each pair of nodes in T
array[1..N] of var 0..N: chain;
%array[1..N, 1..N, 1..N] of var 0..1: inPath; % inPath[x, y, z] iff x <= y <= z (in the sense that y is in path(x->z) in T)
%array[1..N] of var 0..N-1: height; % height[x] of each node x in T



constraint alldifferent_except_0(chain);



%% build a proper tree of n nodes
constraint parent[1] = 0 /\ depth[1] = 0; % 1 is root
constraint forall(x in 2..n)( parent[x] > 0 /\ depth[x] > 0 ); % each node (!= root) has a parent and a positive depth
constraint forall(x in n+1..N)( parent[x] = 0 /\ depth[x] = 0 ); % set proper constants to nodes not in T
constraint forall(x in 2..n)( parent[x] < x ); % symmetry breaking constraint (enum nodes of T from top to bottom)
constraint forall(x in 2..n)( depth[x] = depth[parent[x]]+1 ); % relates depths and parents
constraint non_decreasing_except_0(depth);
%constraint forall(x in 2..n)( 
%      height[parent[x]] > height[x] /\ % parent has height greater then all his children
%      height[x] < n-1                  % non-root nodes has at most height n-2
%);
constraint exists(x in 2..n)( parent[x] = 1 ); % root has at least a son

%% Set of constraints for ancestor
constraint forall(x in 1..N, y in n+1..N)(
      ancestor[x, y] = 0 /\
      ancestor[y, x] = 0
);
constraint forall(x in 2..n)(
      ancestor[parent[x], x] = 1 /\
      ancestor[1, x] = 1
);
constraint forall(x,y in 1..n where x<=y)( ancestor[y, x] = 0 );
constraint forall(x,y in 1..n where x<y)(
      (ancestor[x, y] = 1)
      <-> (x = parent[y] \/ ancestor[x, parent[y]] = 1)
);

%% Set of constraints for lca
constraint forall(x in 1..N, y in n+1..N)(
      lca[x, y] = 0 /\
      lca[y, x] = 0
);
constraint forall(x,y in 1..n where x<y)(
      lca[x, y] > 0 /\
      lca[x, y] <= x /\
      lca[x, y] <= y
);
constraint forall(x in 2..n)( lca[x, parent[x]] = parent[x] );
constraint forall(x in 1..n)(
      lca[x, 1] = 1 /\
      lca[x, x] = x
);
constraint forall(x,y in 1..n where x<y)( lca[x, y] = lca[y, x] );
constraint forall(x,y in 2..n where x<y)(
      (ancestor[x, y] = 0) -> (lca[x, y] = lca[parent[x], y])
);
constraint forall(x,y in 1..n where x<y)(
      (ancestor[x, y] = 1) -> (lca[x, y] = x)
);

%% relate graph and tree
array[1..N, 1..N] of var 0..1: hasColor; % hasColor(x, y) iff node x of G \in chi(y) of T

% TD1: each node has a color
constraint forall(x in 1..N)(
      exists(k in 1..n)( hasColor[x, k] = 1 )
);

% TD2: if {x, y} \in G, then x and y share a color
constraint forall(x,y in 1..N where x<y /\ graph[x, y]=1)(
      exists(k in 1..n)( hasColor[x, k]=1 /\ hasColor[y, k]=1 )
);


% TD3: if x has colors r and t, then it has colors s in path(r->t)
constraint forall(x in 1..N, r in 1..n where hasColor[x, r]=1, t in r+1..n where hasColor[x, t]=1)(
      forall(s in 1..n where s!=r /\ s!=t)(
            inPath(r, s, t)
            -> (hasColor[x, s] = 1)
      )
); 

%% Extra constraints
constraint forall(x in 1..N, y in n+1..N)( hasColor[x, y] = 0 ); % cannot use colors not in T
constraint forall(y in 1..n)( % if a color is in T, then it has to be used
      exists(x in 1..N)( hasColor[x, y] = 1 )
);
%constraint forall(r in 2..n, s in 1..r-1 where s=parent[r])(
%      not_subset_one_another(col(hasColor, r), col(hasColor, s))
%);

var 1..N: objective;

constraint objective = max([sum(x in 1..N)( hasColor[x, r] ) | r in 1..n]) -1;


constraint forall(c in 1..n)(
      sum(x in 1..N)( hasColor[x, c] ) = objective+1
);

%% My predicates
predicate non_decreasing_except_0(array[1..N] of var 0..N-1: arr) =
      forall(i in 2..N where arr[i]>0)(
            arr[i] >= arr[i-1]
      );
      
predicate not_subset_one_another(array[1..N] of var 0..1: a, array[1..N] of var 0..1: b) =
      exists(i in 1..n)( a[i]=1 /\ b[i]=0 ) /\
      exists(i in 1..n)( a[i]=0 /\ b[i]=1 );
      
predicate inPath(var 1..N: r, var 1..N: s, var 1..N: t) =
      let {
          var 0..N: l = lca[r, t];
          
      } in (inChain(r, s, l) \/ inChain(t, s, l));
      
predicate inChain(var 1..N: x, var 1..N: y, var 0..N: l) =
      let {
          var 0..N-1: d = depth[x]-depth[y];
          
          constraint forall(i in 1..N where i>=d+2)( chain[i] = 0 );
          constraint chain[1] = x;
          constraint forall(i in 2..d+1)( chain[i] = parent[chain[i-1]] );
          
      } in exists(i in 1..d+1)( chain[i] = y );
      
      %if x==y \/ y==l then true
      %elseif x==l \/ x==0 \/ l==0 then false
      %elseif parent[x]>0 then inChain(parent[x], y, l)
      %else false
      %endif;

% test


solve :: seq_search([
             int_search([n], first_fail, indomain_split, complete),
             int_search(parent ++ depth, first_fail, indomain_min, complete),
             int_search(lca, first_fail, indomain_min, complete),
             int_search(hasColor, impact, indomain_max, complete)])
         minimize objective;

output ["Color \(r): \([x | x in 1..N where fix(hasColor[x, r]) = 1])\n" | r in 1..N where exists(y in 1..N)(fix(hasColor[y, r])=1)] ++
       ["Tree:  \(parent)\nDepth: \(depth)\nObj = \(objective)"];