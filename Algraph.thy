theory Algraph imports Main
begin

datatype 'a algraph =
  Empty
  | Vertex "'a"
  | Connect "'a algraph" "'a algraph"
  | Overlay "'a algraph" "'a algraph"

fun semant :: "'a algraph \<Rightarrow> (('a *'a) set) * 'a set" where
  "semant Empty =({}, {})"
| "semant (Vertex v) = ({}, {v})"
| "semant (Overlay x y) = 
    (let (x_edges, x_verts) = semant x in
    let (y_edges, y_verts) = semant y in
    (x_edges \<union> y_edges, x_verts \<union> y_verts))"
| "semant (Connect x y) = 
    (let (x_edges, x_verts) = semant x in
    let (y_edges, y_verts) = semant y in
    (x_edges \<union> y_edges \<union> (x_verts \<times> y_verts), x_verts \<union> y_verts))"

fun edge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a algraph" where
  "edge x y = Connect (Vertex x) (Vertex y)"

fun edges :: "('a * 'a) list \<Rightarrow> 'a algraph" where
  "edges l = (
    let edges = map (\<lambda>(x, y). edge x y) l in
    foldr (\<lambda> v acc. Overlay v acc) edges Empty)"

fun vertices  :: "'a list \<Rightarrow> 'a algraph" where
  "vertices l = (
    let verts = map (\<lambda>x. Vertex x) l in
    foldr (\<lambda> v acc. Overlay v acc) verts Empty)"
fun clique  :: "'a list \<Rightarrow> 'a algraph" where
  "clique l = (
    let verts = map (\<lambda>x. Vertex x) l in
    foldr (\<lambda> v acc. Connect v acc) verts Empty)"

fun graph :: "'a list \<Rightarrow> ('a * 'a) list \<Rightarrow> 'a algraph" where
  "graph vs es = Overlay (vertices vs) (edges es)"

fun subgraph :: "'a algraph \<Rightarrow> 'a algraph \<Rightarrow> bool" where
  "subgraph xs ys = (
  let (x_edges,  x_verts) = semant xs in
  let (y_edges, y_verts) = semant ys in
  x_edges \<subseteq> y_edges \<and> x_verts \<subseteq> y_verts)"

fun subgraph' :: "'a algraph \<Rightarrow> 'a algraph \<Rightarrow> bool" where
  "subgraph' xs ys = (semant (Overlay xs ys) = semant ys)"

value "clique [1::nat , 2, 3]"

theorem vertex_dist:
  fixes x
  shows "semant (Vertex x) = semant (vertices [x])"
  by simp

theorem overlay_zero:
  fixes n
  shows "semant (Overlay n Empty) = semant n"
  by simp

theorem edge_clique_rel:
  fixes x y
  shows "semant (edge x y) = semant (clique [x, y])"
  by simp

theorem vert_clique_rel:
  fixes xs
  shows "subgraph (vertices xs) (clique xs)"
proof (induction xs)
  case Nil
  then show ?case  by simp
next
  case (Cons a xs)
  then show ?case by force
qed

theorem subgraph_eq:
  fixes xs ys
  shows "subgraph xs ys = subgraph' xs ys"
  by auto

theorem vert_clique_rel':
  fixes xs
  shows "subgraph' (vertices xs) (clique xs)"
  using subgraph_eq vert_clique_rel by blast

theorem conn_assoc:
  fixes xs ys zs
  shows "semant (Connect (Connect xs ys) zs) = semant (Connect xs (Connect ys zs))"
proof -
  obtain xe xv where xs_sem: "semant xs = (xe, xv)" by (cases "semant xs") auto
  obtain ye yv where ys_sem: "semant ys = (ye, yv)" by (cases "semant ys") auto  
  obtain ze zv where zs_sem: "semant zs = (ze, zv)" by (cases "semant zs") auto
  show ?thesis
    apply(simp add: xs_sem ys_sem zs_sem)
      by blast
qed


theorem clique_conn:
  fixes xs ys
  shows "semant (clique (append xs ys)) = semant (Connect (clique xs) (clique ys)) "
proof
  show 1: "fst (semant (clique (xs @ ys))) = fst (semant (Connect (clique xs) (clique ys)))" 
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case 
    proof -
      obtain xe xv where xs_sem: "semant (foldr Connect (map Vertex xs) Empty) = (xe, xv)"
        by (cases "semant (foldr Connect (map Vertex xs) Empty)") auto
      obtain ye yv where ys_sem: "semant (foldr Connect (map Vertex ys) Empty) = (ye, yv)"  
        by (cases "semant (foldr Connect (map Vertex ys) Empty)") auto
      obtain ze zv where zs_sem: "semant (foldr Connect (map Vertex xs) (foldr Connect (map Vertex ys) Empty)) = (ze, zv)"  
        by (cases "semant (foldr Connect (map Vertex xs) (foldr Connect (map Vertex ys) Empty))") auto
      show ?thesis
        apply(simp add: xs_sem ys_sem zs_sem )
        apply(auto)
        sorry


        
        
    qed
      
  qed
    
  show 2: "snd (semant (clique (xs @ ys))) = snd (semant (Connect (clique xs) (clique ys)))" 
  proof (induction xs)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    then show ?case 
    proof -
      obtain xe xv where xs_sem: "semant (foldr Connect (map Vertex xs) Empty) = (xe, xv)"
        by (cases "semant (foldr Connect (map Vertex xs) Empty)") auto
      obtain ye yv where ys_sem: "semant (foldr Connect (map Vertex ys) Empty) = (ye, yv)"  
        by (cases "semant (foldr Connect (map Vertex ys) Empty)") auto
      obtain ze zv where zs_sem: "semant (foldr Connect (map Vertex xs) (foldr Connect (map Vertex ys) Empty)) = (ze, zv)"  
        by (cases "semant (foldr Connect (map Vertex xs) (foldr Connect (map Vertex ys) Empty))") auto
      show ?thesis
        (*apply(simp add: xs_sem ys_sem zs_sem)*)
        apply(auto)
        try

        sorry
        
    qed
      
  qed
qed

end