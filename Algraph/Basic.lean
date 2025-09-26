import Mathlib

inductive Algraph (α : Type) where
  | empty : Algraph α 
  | vertex : α -> Algraph α 
  | overlay : (Algraph α) -> (Algraph α) -> (Algraph α)
  | connect : (Algraph α) -> (Algraph α) -> (Algraph α)
  deriving Repr

namespace Algraph
open Algraph

def semant : Algraph α -> (Set (α × α)) × Set α
  | Algraph.empty => (∅, ∅)
  | Algraph.vertex v => (∅, {v})
  | Algraph.overlay l r => 
    let (l_edges,  l_verts) := semant l
    let (r_edges, r_verts) := semant r
    ((l_edges ∪ r_edges), (l_verts ∪ r_verts))
  | Algraph.connect l r => 
    let (l_edges,  l_verts) := semant l
    let (r_edges, r_verts) := semant r
    ((l_edges ∪ r_edges ∪ l_verts.prod r_verts), (l_verts ∪ r_verts))


notation "⟪" g "⟫" => semant g

-- For printing and debugging
def fsemant [DecidableEq α] : Algraph α -> (Finset (α × α)) × Finset α
  | Algraph.empty => (∅, ∅)
  | Algraph.vertex v => (∅, {v})
  | Algraph.overlay l r => 
    let (l_edges,  l_verts) := fsemant l
    let (r_edges, r_verts) := fsemant r
    ((l_edges ∪ r_edges), (l_verts ∪ r_verts))
  | Algraph.connect l r => 
    let (l_edges,  l_verts) := fsemant l
    let (r_edges, r_verts) := fsemant r
    ((l_edges ∪ r_edges ∪ l_verts.product r_verts), (l_verts ∪ r_verts))

def edge (x y : α ) : Algraph α  := 
  connect (vertex x) (vertex y)

def edges :  (List (α × α)) -> Algraph α :=
  (List.foldr overlay empty) ∘ (List.map (fun (x, y) => edge x y))

def vertices  : List α  -> Algraph α  := (List.foldr overlay empty) ∘  (List.map vertex)
def clique  : List α  -> Algraph α := 
 (List.foldr connect empty) ∘  (List.map vertex)

def graph  (vs : List α) (es : List (α × α)):  Algraph α :=
  overlay (vertices vs) (edges es)

def subgraph (xs ys : Algraph α) :=
  let (x_edges,  x_verts) := semant xs
  let (y_edges, y_verts) := semant ys
  x_edges ⊆ y_edges /\ x_verts ⊆ y_verts

def subgraph' (xs ys : Algraph α) :=
  ⟪overlay xs ys⟫ = ⟪ys⟫

def testEdge := edge 1 2 

def testVertices := vertices [1, 2, 3, 4, 5]

def testClique := clique [1, 2, 3]

#eval testEdge
#eval testVertices
#eval testClique
#eval (fsemant testClique)


theorem overlay_zero (n : Algraph α) : ⟪overlay n empty⟫ = ⟪n⟫  := 
  by
    simp [semant]

theorem vertex_dist : semant (vertex x) = semant (vertices [x]) := 
  by 
    simp [semant, vertices]

theorem edge_clique_rel : ⟪edge x y⟫ = ⟪clique [x, y]⟫ := 
  by 
    simp [semant, clique, edge, Set.prod]

theorem vert_clique_rel : subgraph (vertices xs) (clique xs) :=
  by
    simp [subgraph, vertices, clique]
    induction xs with
    | nil => 
      rw [List.map_nil]
      rw [List.foldr_nil]
      rw [List.foldr_nil]
      rw [semant]
      simp
    | cons head tail ih => 
      repeat (simp_all ; rw [semant])
      grind

theorem subgraph_eq : subgraph xs ys  = subgraph' xs ys := 
  by
    rw [subgraph']
    rw [ semant]
    simp []
    rw [subgraph]
    simp_all
    apply Iff.intro
    case mp := by
      intro sg
      have xs_subset_ys : ⟪xs⟫.1 ⊆ ⟪ys⟫.1 ∧ ⟪xs⟫.2 ⊆ ⟪ys⟫.2 := sg
      have nodes_subset : ⟪xs⟫.1 ⊆ ⟪ys⟫.1 := xs_subset_ys.1
      have edges_subset : ⟪xs⟫.2 ⊆ ⟪ys⟫.2 := xs_subset_ys.2
      rw [Set.union_eq_self_of_subset_left]
      rw [Set.union_eq_self_of_subset_left]
      exact edges_subset
      exact nodes_subset 
    case mpr := by
      intro sg
      have xs_un_ys : (⟪xs⟫.1 ∪ ⟪ys⟫.1, ⟪xs⟫.2 ∪ ⟪ys⟫.2) = ⟪ys⟫ := sg
      have y1: (⟪xs⟫.1 ∪ ⟪ys⟫.1, ⟪xs⟫.2 ∪ ⟪ys⟫.2).1 = ⟪ys⟫.1
      have y1: (⟪xs⟫.1 ∪ ⟪ys⟫.1, ⟪xs⟫.2 ∪ ⟪ys⟫.2).2 = ⟪ys⟫.2
      repeat (simp_all ; grind)

theorem vert_clique_rel' : subgraph' (vertices xs) (clique xs) := 
  by
    rw [<- subgraph_eq]
    exact vert_clique_rel

lemma left_ident : ⟪connect x empty⟫ = ⟪x⟫ := by
  simp [semant, Set.prod]

lemma right_ident : ⟪connect empty x⟫ = ⟪x⟫ := by
  simp [semant, Set.prod]

lemma conn_assoc : ⟪connect (connect x y) z⟫ = ⟪connect x (connect y z)⟫ := by
  simp only [semant]
  generalize semant x = sx
  generalize semant y = sy  
  generalize semant z = sz
  cases sx with | mk xe xv =>
  cases sy with | mk ye yv =>
  cases sz with | mk ze zv =>
  simp_all only [Prod.mk.injEq]
  apply And.intro

  · have h1 : (xv ∪ yv).prod zv = xv.prod zv ∪ yv.prod zv := by
      ext ⟨a, b⟩
      simp only [Set.mem_union]
      constructor
      · intro ⟨h1, h2⟩
        cases h1 with
        | inl h => left; exact ⟨h, h2⟩
        | inr h => right; exact ⟨h, h2⟩
      · intro h
        cases h with
        | inl h => exact ⟨Or.inl h.1, h.2⟩
        | inr h => exact ⟨Or.inr h.1, h.2⟩
    
    have h2 : xv.prod (yv ∪ zv) = xv.prod yv ∪ xv.prod zv := by
      ext ⟨a, b⟩
      simp only [Set.mem_union]
      constructor
      · intro ⟨h1, h2⟩
        cases h2 with
        | inl h => left; exact ⟨h1, h⟩
        | inr h => right; exact ⟨h1, h⟩
      · intro h
        cases h with
        | inl h => exact ⟨h.1, Or.inl h.2⟩
        | inr h => exact ⟨h.1, Or.inr h.2⟩
    
    rw [h1, h2]
    simp only [Set.union_comm, Set.union_left_comm]

  · exact Set.union_assoc xv yv zv

lemma clique_empty : ⟪ clique ([]:List α) ⟫ = ⟪ empty ⟫ := by
  simp [clique, semant]

lemma connect_congr_right (x : Algraph α) {y z : Algraph α} (h : ⟪y⟫ = ⟪z⟫) : 
    ⟪connect x y⟫ = ⟪connect x z⟫ := by
  simp [semant]
  rw [h]
  simp [Set.prod]

-- Agraph with connect is a monoid it seems
theorem clique_conn :
    ⟪clique (xs ++ ys)⟫ = ⟪connect (clique xs) (clique ys)⟫ := by
      induction xs with
      | nil => 
        simp [semant]
        simp [Set.prod.eq_def]
        simp [clique_empty]
        rw [semant]
        simp

      | cons x xs' ih =>
          have clique_cons : clique (x :: xs') = connect (vertex x) (clique xs') := by
            simp [clique, List.map_cons, List.foldr_cons]
          
          rw [List.cons_append]
          rw [clique_cons]
          simp [clique]

          have foldr_eq : List.foldr connect (List.foldr connect empty (List.map vertex ys)) (List.map vertex xs') = 
                          clique (xs' ++ ys) := by
            simp [clique, List.map_append, List.foldr_append]

          rw [foldr_eq]
          rw [connect_congr_right (vertex x) ih]
          simp [conn_assoc]
          rfl

end Algraph

#eval ([1, 2, 3, 4].foldr (· + ·) 0)
#eval (([1, 2] ++ [ 3, 4]).foldr (· + ·) 0)
#eval (([ 3, 4]).foldr (· + ·) 0)
#eval (([ 1, 2]).foldr (· + ·) 0)
