import CompCert4Lean.Lib.Coqlib

/-!
# Applicative finite maps

This module is the definition-translation surface for CompCert's `lib/Maps.v`.
The computational tree and map operations are source-shaped; proof-heavy
source declarations are represented below by exact statement descriptors.
-/

namespace CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

namespace PTree

def elt : Type := positive
def elt_eq (a b : elt) : CompCert4Lean.Foundation.Logic.Support.Sumbool (a = b) (a ≠ b) :=
  peq a b

inductive tree' (A : Type) : Type where
  | Node001 : tree' A → tree' A
  | Node010 : A → tree' A
  | Node011 : A → tree' A → tree' A
  | Node100 : tree' A → tree' A
  | Node101 : tree' A → tree' A → tree' A
  | Node110 : tree' A → A → tree' A
  | Node111 : tree' A → A → tree' A → tree' A

inductive tree (A : Type) : Type where
  | Empty : tree A
  | Nodes : tree' A → tree A

export tree (Empty Nodes)
export tree' (Node001 Node010 Node011 Node100 Node101 Node110 Node111)

abbrev t (A : Type) : Type := tree A

def Node {A : Type} (l : tree A) (o : Option A) (r : tree A) : tree A :=
  match l, o, r with
  | .Empty, none, .Empty => .Empty
  | .Empty, none, .Nodes r' => .Nodes (.Node001 r')
  | .Empty, some x, .Empty => .Nodes (.Node010 x)
  | .Empty, some x, .Nodes r' => .Nodes (.Node011 x r')
  | .Nodes l', none, .Empty => .Nodes (.Node100 l')
  | .Nodes l', none, .Nodes r' => .Nodes (.Node101 l' r')
  | .Nodes l', some x, .Empty => .Nodes (.Node110 l' x)
  | .Nodes l', some x, .Nodes r' => .Nodes (.Node111 l' x r')

def empty (A : Type) : t A := .Empty

def get' {A : Type} : positive → tree' A → Option A
  | .xH, .Node001 _ => none
  | .xH, .Node010 x => some x
  | .xH, .Node011 x _ => some x
  | .xH, .Node100 _ => none
  | .xH, .Node101 _ _ => none
  | .xH, .Node110 _ x => some x
  | .xH, .Node111 _ x _ => some x
  | .xO q, .Node001 _ => none
  | .xO q, .Node010 _ => none
  | .xO q, .Node011 _ _ => none
  | .xO q, .Node100 m => get' q m
  | .xO q, .Node101 m _ => get' q m
  | .xO q, .Node110 m _ => get' q m
  | .xO q, .Node111 m _ _ => get' q m
  | .xI q, .Node001 m => get' q m
  | .xI q, .Node010 _ => none
  | .xI q, .Node011 _ m => get' q m
  | .xI q, .Node100 _ => none
  | .xI q, .Node101 _ m => get' q m
  | .xI q, .Node110 _ _ => none
  | .xI q, .Node111 _ _ m => get' q m

def get {A : Type} (p : positive) (m : tree A) : Option A :=
  match m with
  | .Empty => none
  | .Nodes m' => get' p m'

def set0 {A : Type} : positive → A → tree' A
  | .xH, x => .Node010 x
  | .xO q, x => .Node100 (set0 q x)
  | .xI q, x => .Node001 (set0 q x)

def set' {A : Type} : positive → A → tree' A → tree' A
  | .xH, x, .Node001 r => .Node011 x r
  | .xH, x, .Node010 _ => .Node010 x
  | .xH, x, .Node011 _ r => .Node011 x r
  | .xH, x, .Node100 l => .Node110 l x
  | .xH, x, .Node101 l r => .Node111 l x r
  | .xH, x, .Node110 l _ => .Node110 l x
  | .xH, x, .Node111 l _ r => .Node111 l x r
  | .xO q, x, .Node001 r => .Node101 (set0 q x) r
  | .xO q, x, .Node010 y => .Node110 (set0 q x) y
  | .xO q, x, .Node011 y r => .Node111 (set0 q x) y r
  | .xO q, x, .Node100 l => .Node100 (set' q x l)
  | .xO q, x, .Node101 l r => .Node101 (set' q x l) r
  | .xO q, x, .Node110 l y => .Node110 (set' q x l) y
  | .xO q, x, .Node111 l y r => .Node111 (set' q x l) y r
  | .xI q, x, .Node001 r => .Node001 (set' q x r)
  | .xI q, x, .Node010 y => .Node011 y (set0 q x)
  | .xI q, x, .Node011 y r => .Node011 y (set' q x r)
  | .xI q, x, .Node100 l => .Node101 l (set0 q x)
  | .xI q, x, .Node101 l r => .Node101 l (set' q x r)
  | .xI q, x, .Node110 l y => .Node111 l y (set0 q x)
  | .xI q, x, .Node111 l y r => .Node111 l y (set' q x r)

def set {A : Type} (p : positive) (x : A) (m : tree A) : tree A :=
  match m with
  | .Empty => .Nodes (set0 p x)
  | .Nodes m' => .Nodes (set' p x m')

def rem' {A : Type} : positive → tree' A → tree A
  | .xH, .Node001 r => .Nodes (.Node001 r)
  | .xH, .Node010 _ => .Empty
  | .xH, .Node011 _ r => .Nodes (.Node001 r)
  | .xH, .Node100 l => .Nodes (.Node100 l)
  | .xH, .Node101 l r => .Nodes (.Node101 l r)
  | .xH, .Node110 l _ => .Nodes (.Node100 l)
  | .xH, .Node111 l _ r => .Nodes (.Node101 l r)
  | .xO q, .Node001 r => .Nodes (.Node001 r)
  | .xO q, .Node010 y => .Nodes (.Node010 y)
  | .xO q, .Node011 y r => .Nodes (.Node011 y r)
  | .xO q, .Node100 l => Node (rem' q l) none .Empty
  | .xO q, .Node101 l r => Node (rem' q l) none (.Nodes r)
  | .xO q, .Node110 l y => Node (rem' q l) (some y) .Empty
  | .xO q, .Node111 l y r => Node (rem' q l) (some y) (.Nodes r)
  | .xI q, .Node001 r => Node .Empty none (rem' q r)
  | .xI q, .Node010 y => .Nodes (.Node010 y)
  | .xI q, .Node011 y r => Node .Empty (some y) (rem' q r)
  | .xI q, .Node100 l => .Nodes (.Node100 l)
  | .xI q, .Node101 l r => Node (.Nodes l) none (rem' q r)
  | .xI q, .Node110 l y => .Nodes (.Node110 l y)
  | .xI q, .Node111 l y r => Node (.Nodes l) (some y) (rem' q r)

def remove' {A : Type} : positive → tree' A → tree A
  | .xI q, .Node001 r =>
      match remove' q r with
      | .Empty => .Empty
      | .Nodes r' => .Nodes (.Node001 r')
  | .xI q, .Node010 y => .Nodes (.Node010 y)
  | .xI q, .Node011 y r =>
      match remove' q r with
      | .Empty => .Nodes (.Node010 y)
      | .Nodes r' => .Nodes (.Node011 y r')
  | .xI q, .Node100 l => .Nodes (.Node100 l)
  | .xI q, .Node101 l r =>
      match remove' q r with
      | .Empty => .Nodes (.Node100 l)
      | .Nodes r' => .Nodes (.Node101 l r')
  | .xI q, .Node110 l y => .Nodes (.Node110 l y)
  | .xI q, .Node111 l y r =>
      match remove' q r with
      | .Empty => .Nodes (.Node110 l y)
      | .Nodes r' => .Nodes (.Node111 l y r')
  | .xO q, .Node001 r => .Nodes (.Node001 r)
  | .xO q, .Node010 y => .Nodes (.Node010 y)
  | .xO q, .Node011 y r => .Nodes (.Node011 y r)
  | .xO q, .Node100 l =>
      match remove' q l with
      | .Empty => .Empty
      | .Nodes l' => .Nodes (.Node100 l')
  | .xO q, .Node101 l r =>
      match remove' q l with
      | .Empty => .Nodes (.Node001 r)
      | .Nodes l' => .Nodes (.Node101 l' r)
  | .xO q, .Node110 l y =>
      match remove' q l with
      | .Empty => .Nodes (.Node010 y)
      | .Nodes l' => .Nodes (.Node110 l' y)
  | .xO q, .Node111 l y r =>
      match remove' q l with
      | .Empty => .Nodes (.Node011 y r)
      | .Nodes l' => .Nodes (.Node111 l' y r)
  | .xH, .Node001 r => .Nodes (.Node001 r)
  | .xH, .Node010 y => .Empty
  | .xH, .Node011 _ r => .Nodes (.Node001 r)
  | .xH, .Node100 l => .Nodes (.Node100 l)
  | .xH, .Node101 l r => .Nodes (.Node101 l r)
  | .xH, .Node110 l _ => .Nodes (.Node100 l)
  | .xH, .Node111 l _ r => .Nodes (.Node101 l r)

def remove {A : Type} (p : positive) (m : tree A) : tree A :=
  match m with
  | .Empty => .Empty
  | .Nodes m' => remove' p m'

def not_trivially_empty {A : Type} (l : tree A) (o : Option A) (r : tree A) : Prop :=
  match l, o, r with
  | .Empty, none, .Empty => False
  | _, _, _ => True

def tree_rec' {A B : Type} (emptyCase : B)
    (node : tree A → B → Option A → tree A → B → B) : tree' A → B
  | .Node001 r => node .Empty emptyCase none (.Nodes r) (tree_rec' emptyCase node r)
  | .Node010 x => node .Empty emptyCase (some x) .Empty emptyCase
  | .Node011 x r => node .Empty emptyCase (some x) (.Nodes r) (tree_rec' emptyCase node r)
  | .Node100 l => node (.Nodes l) (tree_rec' emptyCase node l) none .Empty emptyCase
  | .Node101 l r => node (.Nodes l) (tree_rec' emptyCase node l) none (.Nodes r) (tree_rec' emptyCase node r)
  | .Node110 l x => node (.Nodes l) (tree_rec' emptyCase node l) (some x) .Empty emptyCase
  | .Node111 l x r => node (.Nodes l) (tree_rec' emptyCase node l) (some x) (.Nodes r) (tree_rec' emptyCase node r)

def tree_rec {A B : Type} (emptyCase : B)
    (node : tree A → B → Option A → tree A → B → B) (m : tree A) : B :=
  match m with
  | .Empty => emptyCase
  | .Nodes m' => tree_rec' emptyCase node m'

def tree_rec2' {A B C : Type} (base : C) (base1 : tree B → C) (base2 : tree A → C)
    (nodes : tree A → Option A → tree A → tree B → Option B → tree B → C → C → C) :
    tree' A → tree' B → C
  | .Node001 l1, .Node001 l2 => nodes .Empty none (.Nodes l1) .Empty none (.Nodes l2) (base) (tree_rec2' base base1 base2 nodes l1 l2)
  | .Node001 l1, .Node010 x2 => nodes .Empty none (.Nodes l1) .Empty (some x2) .Empty (base) (base2 (.Nodes l1))
  | .Node001 l1, .Node011 x2 r2 => nodes .Empty none (.Nodes l1) .Empty (some x2) (.Nodes r2) (base) (tree_rec2' base base1 base2 nodes l1 r2)
  | .Node001 l1, .Node100 l2 => nodes .Empty none (.Nodes l1) (.Nodes l2) none .Empty (base1 (.Nodes l2)) (base2 (.Nodes l1))
  | .Node001 l1, .Node101 l2 r2 => nodes .Empty none (.Nodes l1) (.Nodes l2) none (.Nodes r2) (base1 (.Nodes l2)) (tree_rec2' base base1 base2 nodes l1 r2)
  | .Node001 l1, .Node110 l2 x2 => nodes .Empty none (.Nodes l1) (.Nodes l2) (some x2) .Empty (base1 (.Nodes l2)) (base2 (.Nodes l1))
  | .Node001 l1, .Node111 l2 x2 r2 => nodes .Empty none (.Nodes l1) (.Nodes l2) (some x2) (.Nodes r2) (base1 (.Nodes l2)) (tree_rec2' base base1 base2 nodes l1 r2)
  | .Node010 x1, .Node001 l2 => nodes .Empty (some x1) .Empty .Empty none (.Nodes l2) (base) (base1 (.Nodes l2))
  | .Node010 x1, .Node010 x2 => nodes .Empty (some x1) .Empty .Empty (some x2) .Empty (base) (base)
  | .Node010 x1, .Node011 x2 r2 => nodes .Empty (some x1) .Empty .Empty (some x2) (.Nodes r2) (base) (base1 (.Nodes r2))
  | .Node010 x1, .Node100 l2 => nodes .Empty (some x1) .Empty (.Nodes l2) none .Empty (base1 (.Nodes l2)) (base)
  | .Node010 x1, .Node101 l2 r2 => nodes .Empty (some x1) .Empty (.Nodes l2) none (.Nodes r2) (base1 (.Nodes l2)) (base1 (.Nodes r2))
  | .Node010 x1, .Node110 l2 x2 => nodes .Empty (some x1) .Empty (.Nodes l2) (some x2) .Empty (base1 (.Nodes l2)) (base)
  | .Node010 x1, .Node111 l2 x2 r2 => nodes .Empty (some x1) .Empty (.Nodes l2) (some x2) (.Nodes r2) (base1 (.Nodes l2)) (base1 (.Nodes r2))
  | .Node011 x1 r1, .Node001 l2 => nodes .Empty (some x1) (.Nodes r1) .Empty none (.Nodes l2) (base) (tree_rec2' base base1 base2 nodes r1 l2)
  | .Node011 x1 r1, .Node010 x2 => nodes .Empty (some x1) (.Nodes r1) .Empty (some x2) .Empty (base) (base2 (.Nodes r1))
  | .Node011 x1 r1, .Node011 x2 r2 => nodes .Empty (some x1) (.Nodes r1) .Empty (some x2) (.Nodes r2) (base) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node011 x1 r1, .Node100 l2 => nodes .Empty (some x1) (.Nodes r1) (.Nodes l2) none .Empty (base1 (.Nodes l2)) (base2 (.Nodes r1))
  | .Node011 x1 r1, .Node101 l2 r2 => nodes .Empty (some x1) (.Nodes r1) (.Nodes l2) none (.Nodes r2) (base1 (.Nodes l2)) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node011 x1 r1, .Node110 l2 x2 => nodes .Empty (some x1) (.Nodes r1) (.Nodes l2) (some x2) .Empty (base1 (.Nodes l2)) (base2 (.Nodes r1))
  | .Node011 x1 r1, .Node111 l2 x2 r2 => nodes .Empty (some x1) (.Nodes r1) (.Nodes l2) (some x2) (.Nodes r2) (base1 (.Nodes l2)) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node100 l1, .Node001 l2 => nodes (.Nodes l1) none .Empty .Empty none (.Nodes l2) (base2 (.Nodes l1)) (base1 (.Nodes l2))
  | .Node100 l1, .Node010 x2 => nodes (.Nodes l1) none .Empty .Empty (some x2) .Empty (base2 (.Nodes l1)) (base)
  | .Node100 l1, .Node011 x2 r2 => nodes (.Nodes l1) none .Empty .Empty (some x2) (.Nodes r2) (base2 (.Nodes l1)) (base1 (.Nodes r2))
  | .Node100 l1, .Node100 l2 => nodes (.Nodes l1) none .Empty (.Nodes l2) none .Empty (tree_rec2' base base1 base2 nodes l1 l2) (base)
  | .Node100 l1, .Node101 l2 r2 => nodes (.Nodes l1) none .Empty (.Nodes l2) none (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (base1 (.Nodes r2))
  | .Node100 l1, .Node110 l2 x2 => nodes (.Nodes l1) none .Empty (.Nodes l2) (some x2) .Empty (tree_rec2' base base1 base2 nodes l1 l2) (base)
  | .Node100 l1, .Node111 l2 x2 r2 => nodes (.Nodes l1) none .Empty (.Nodes l2) (some x2) (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (base1 (.Nodes r2))
  | .Node101 l1 r1, .Node001 l2 => nodes (.Nodes l1) none (.Nodes r1) .Empty none (.Nodes l2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes r1 l2)
  | .Node101 l1 r1, .Node010 x2 => nodes (.Nodes l1) none (.Nodes r1) .Empty (some x2) .Empty (base2 (.Nodes l1)) (base2 (.Nodes r1))
  | .Node101 l1 r1, .Node011 x2 r2 => nodes (.Nodes l1) none (.Nodes r1) .Empty (some x2) (.Nodes r2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node101 l1 r1, .Node100 l2 => nodes (.Nodes l1) none (.Nodes r1) (.Nodes l2) none .Empty (tree_rec2' base base1 base2 nodes l1 l2) (base2 (.Nodes r1))
  | .Node101 l1 r1, .Node101 l2 r2 => nodes (.Nodes l1) none (.Nodes r1) (.Nodes l2) none (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node101 l1 r1, .Node110 l2 x2 => nodes (.Nodes l1) none (.Nodes r1) (.Nodes l2) (some x2) .Empty (tree_rec2' base base1 base2 nodes l1 l2) (base2 (.Nodes r1))
  | .Node101 l1 r1, .Node111 l2 x2 r2 => nodes (.Nodes l1) none (.Nodes r1) (.Nodes l2) (some x2) (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node110 l1 x1, .Node001 l2 => nodes (.Nodes l1) (some x1) .Empty .Empty none (.Nodes l2) (base2 (.Nodes l1)) (base1 (.Nodes l2))
  | .Node110 l1 x1, .Node010 x2 => nodes (.Nodes l1) (some x1) .Empty .Empty (some x2) .Empty (base2 (.Nodes l1)) (base)
  | .Node110 l1 x1, .Node011 x2 r2 => nodes (.Nodes l1) (some x1) .Empty .Empty (some x2) (.Nodes r2) (base2 (.Nodes l1)) (base1 (.Nodes r2))
  | .Node110 l1 x1, .Node100 l2 => nodes (.Nodes l1) (some x1) .Empty (.Nodes l2) none .Empty (tree_rec2' base base1 base2 nodes l1 l2) (base)
  | .Node110 l1 x1, .Node101 l2 r2 => nodes (.Nodes l1) (some x1) .Empty (.Nodes l2) none (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (base1 (.Nodes r2))
  | .Node110 l1 x1, .Node110 l2 x2 => nodes (.Nodes l1) (some x1) .Empty (.Nodes l2) (some x2) .Empty (tree_rec2' base base1 base2 nodes l1 l2) (base)
  | .Node110 l1 x1, .Node111 l2 x2 r2 => nodes (.Nodes l1) (some x1) .Empty (.Nodes l2) (some x2) (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (base1 (.Nodes r2))
  | .Node111 l1 x1 r1, .Node001 l2 => nodes (.Nodes l1) (some x1) (.Nodes r1) .Empty none (.Nodes l2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes r1 l2)
  | .Node111 l1 x1 r1, .Node010 x2 => nodes (.Nodes l1) (some x1) (.Nodes r1) .Empty (some x2) .Empty (base2 (.Nodes l1)) (base2 (.Nodes r1))
  | .Node111 l1 x1 r1, .Node011 x2 r2 => nodes (.Nodes l1) (some x1) (.Nodes r1) .Empty (some x2) (.Nodes r2) (base2 (.Nodes l1)) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node111 l1 x1 r1, .Node100 l2 => nodes (.Nodes l1) (some x1) (.Nodes r1) (.Nodes l2) none .Empty (tree_rec2' base base1 base2 nodes l1 l2) (base2 (.Nodes r1))
  | .Node111 l1 x1 r1, .Node101 l2 r2 => nodes (.Nodes l1) (some x1) (.Nodes r1) (.Nodes l2) none (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 r2)
  | .Node111 l1 x1 r1, .Node110 l2 x2 => nodes (.Nodes l1) (some x1) (.Nodes r1) (.Nodes l2) (some x2) .Empty (tree_rec2' base base1 base2 nodes l1 l2) (base2 (.Nodes r1))
  | .Node111 l1 x1 r1, .Node111 l2 x2 r2 => nodes (.Nodes l1) (some x1) (.Nodes r1) (.Nodes l2) (some x2) (.Nodes r2) (tree_rec2' base base1 base2 nodes l1 l2) (tree_rec2' base base1 base2 nodes r1 r2)

def tree_rec2 {A B C : Type} (base : C) (base1 : tree B → C) (base2 : tree A → C)
    (nodes : tree A → Option A → tree A → tree B → Option B → tree B → C → C → C)
    (a : tree A) (b : tree B) : C :=
  match a, b with
  | .Empty, .Empty => base
  | .Empty, _ => base1 b
  | _, .Empty => base2 a
  | .Nodes a', .Nodes b' => tree_rec2' base base1 base2 nodes a' b'

def tree_ind' {A : Type} (P : tree A → Type) (emptyCase : P .Empty)
    (node : ∀ l, P l → ∀ o r, P r → not_trivially_empty l o r → P (Node l o r)) :
    (m : tree' A) → P (.Nodes m)
  | .Node001 r => node .Empty emptyCase none (.Nodes r) (tree_ind' P emptyCase node r) trivial
  | .Node010 x => node .Empty emptyCase (some x) .Empty emptyCase trivial
  | .Node011 x r => node .Empty emptyCase (some x) (.Nodes r) (tree_ind' P emptyCase node r) trivial
  | .Node100 l => node (.Nodes l) (tree_ind' P emptyCase node l) none .Empty emptyCase trivial
  | .Node101 l r => node (.Nodes l) (tree_ind' P emptyCase node l) none (.Nodes r) (tree_ind' P emptyCase node r) trivial
  | .Node110 l x => node (.Nodes l) (tree_ind' P emptyCase node l) (some x) .Empty emptyCase trivial
  | .Node111 l x r => node (.Nodes l) (tree_ind' P emptyCase node l) (some x) (.Nodes r) (tree_ind' P emptyCase node r) trivial

def tree_ind {A : Type} (P : tree A → Type) (emptyCase : P .Empty)
    (node : ∀ l, P l → ∀ o r, P r → not_trivially_empty l o r → P (Node l o r))
    (m : tree A) : P m :=
  match m with
  | .Empty => emptyCase
  | .Nodes m' => tree_ind' P emptyCase node m'

def prev_append : positive → positive → positive
  | .xH, j => j
  | .xI i, j => prev_append i (.xI j)
  | .xO i, j => prev_append i (.xO j)

def prev (i : positive) : positive := prev_append i .xH

def map' {A B : Type} (f : positive → A → B) : tree' A → positive → tree' B
  | .Node001 r, i => .Node001 (map' f r (.xI i))
  | .Node010 x, i => .Node010 (f (prev i) x)
  | .Node011 x r, i => .Node011 (f (prev i) x) (map' f r (.xI i))
  | .Node100 l, i => .Node100 (map' f l (.xO i))
  | .Node101 l r, i => .Node101 (map' f l (.xO i)) (map' f r (.xI i))
  | .Node110 l x, i => .Node110 (map' f l (.xO i)) (f (prev i) x)
  | .Node111 l x r, i => .Node111 (map' f l (.xO i)) (f (prev i) x) (map' f r (.xI i))

def map {A B : Type} (f : positive → A → B) (m : tree A) : tree B :=
  match m with
  | .Empty => .Empty
  | .Nodes m' => .Nodes (map' f m' .xH)

def map1' {A B : Type} (f : A → B) : tree' A → tree' B
  | .Node001 r => .Node001 (map1' f r)
  | .Node010 x => .Node010 (f x)
  | .Node011 x r => .Node011 (f x) (map1' f r)
  | .Node100 l => .Node100 (map1' f l)
  | .Node101 l r => .Node101 (map1' f l) (map1' f r)
  | .Node110 l x => .Node110 (map1' f l) (f x)
  | .Node111 l x r => .Node111 (map1' f l) (f x) (map1' f r)

def map1 {A B : Type} (f : A → B) (m : tree A) : tree B :=
  match m with
  | .Empty => .Empty
  | .Nodes m' => .Nodes (map1' f m')

def map_filter1_nonopt {A B : Type} (f : A → Option B) (m : tree A) : tree B :=
  tree_rec .Empty
    (fun l lrec o r rrec =>
      Node lrec (match o with | none => none | some a => f a) rrec) m

def map_filter1 {A B : Type} (f : A → Option B) (m : tree A) : tree B :=
  match m with
  | .Empty => .Empty
  | .Nodes m' =>
      let rec go : tree' A → tree B
        | .Node001 r =>
            match go r with
            | .Empty => .Empty
            | .Nodes r' => .Nodes (.Node001 r')
        | .Node010 x =>
            match f x with
            | some y => .Nodes (.Node010 y)
            | none => .Empty
        | .Node011 x r =>
            match f x with
            | some y =>
                match go r with
                | .Empty => .Nodes (.Node010 y)
                | .Nodes r' => .Nodes (.Node011 y r')
            | none =>
                match go r with
                | .Empty => .Empty
                | .Nodes r' => .Nodes (.Node001 r')
        | .Node100 l =>
            match go l with
            | .Empty => .Empty
            | .Nodes l' => .Nodes (.Node100 l')
        | .Node101 l r =>
            match go l with
            | .Empty =>
                match go r with
                | .Empty => .Empty
                | .Nodes r' => .Nodes (.Node001 r')
            | .Nodes l' =>
                match go r with
                | .Empty => .Nodes (.Node100 l')
                | .Nodes r' => .Nodes (.Node101 l' r')
        | .Node110 l x =>
            match go l with
            | .Empty =>
                match f x with
                | some y => .Nodes (.Node010 y)
                | none => .Empty
            | .Nodes l' =>
                match f x with
                | some y => .Nodes (.Node110 l' y)
                | none => .Nodes (.Node100 l')
        | .Node111 l x r =>
            match go l with
            | .Empty =>
                match f x with
                | some y =>
                    match go r with
                    | .Empty => .Nodes (.Node010 y)
                    | .Nodes r' => .Nodes (.Node011 y r')
                | none =>
                    match go r with
                    | .Empty => .Empty
                    | .Nodes r' => .Nodes (.Node001 r')
            | .Nodes l' =>
                match f x with
                | some y =>
                    match go r with
                    | .Empty => .Nodes (.Node110 l' y)
                    | .Nodes r' => .Nodes (.Node111 l' y r')
                | none =>
                    match go r with
                    | .Empty => .Nodes (.Node100 l')
                    | .Nodes r' => .Nodes (.Node101 l' r')
      go m'

def beq' {A : Type} (beqA : A → A → Bool) : tree' A → tree' A → Bool
  | .Node001 r₁, .Node001 r₂ => beq' beqA r₁ r₂
  | .Node010 x₁, .Node010 x₂ => beqA x₁ x₂
  | .Node011 x₁ r₁, .Node011 x₂ r₂ => beqA x₁ x₂ && beq' beqA r₁ r₂
  | .Node100 l₁, .Node100 l₂ => beq' beqA l₁ l₂
  | .Node101 l₁ r₁, .Node101 l₂ r₂ => beq' beqA l₁ l₂ && beq' beqA r₁ r₂
  | .Node110 l₁ x₁, .Node110 l₂ x₂ => beqA x₁ x₂ && beq' beqA l₁ l₂
  | .Node111 l₁ x₁ r₁, .Node111 l₂ x₂ r₂ =>
      beqA x₁ x₂ && beq' beqA l₁ l₂ && beq' beqA r₁ r₂
  | _, _ => false

def beq {A : Type} (beqA : A → A → Bool) : t A → t A → Bool
  | .Empty, .Empty => true
  | .Nodes m₁, .Nodes m₂ => beq' beqA m₁ m₂
  | _, _ => false

def beq_correct : Prop :=
  ∀ {A : Type} (beqA : A → A → Bool) (m₁ m₂ : t A),
    beq beqA m₁ m₂ = true ↔
      ∀ x : elt,
        match get x m₁, get x m₂ with
        | none, none => True
        | some y₁, some y₂ => beqA y₁ y₂ = true
        | _, _ => False

def beq_correctStatement : Prop := beq_correct

def beq_correct_boolStatement : Prop :=
  ∀ {A : Type} (beqA : A → A → Bool) (m₁ m₂ : t A),
    beq beqA m₁ m₂ = true ↔
      ∀ x : elt,
        (match get x m₁, get x m₂ with
        | none, none => true
        | some y₁, some y₂ => beqA y₁ y₂
        | _, _ => false
        ) = true

def combine {A B C : Type} (f : Option A → Option B → Option C)
    (m1 : tree A) (m2 : tree B) : tree C :=
  let combine_l := map_filter1 (fun a => f (some a) none)
  let combine_r := map_filter1 (fun b => f none (some b))
  match m1 with
  | .Empty =>
      match m2 with
      | .Empty => .Empty
      | .Nodes _ => combine_r m2
  | .Nodes a' =>
      match m2 with
      | .Empty => combine_l m1
      | .Nodes b' =>
          let rec go : tree' A → tree' B → tree C
            | .Node001 l1, .Node001 l2 =>
                Node .Empty none (go l1 l2)
            | .Node001 l1, .Node010 x2 =>
                Node .Empty (f none (some x2)) (combine_l (.Nodes l1))
            | .Node001 l1, .Node011 x2 r2 =>
                Node .Empty (f none (some x2)) (go l1 r2)
            | .Node001 l1, .Node100 l2 =>
                Node (combine_r (.Nodes l2)) none (combine_l (.Nodes l1))
            | .Node001 l1, .Node101 l2 r2 =>
                Node (combine_r (.Nodes l2)) none (go l1 r2)
            | .Node001 l1, .Node110 l2 x2 =>
                Node (combine_r (.Nodes l2)) (f none (some x2)) (combine_l (.Nodes l1))
            | .Node001 l1, .Node111 l2 x2 r2 =>
                Node (combine_r (.Nodes l2)) (f none (some x2)) (go l1 r2)
            | .Node010 x1, .Node001 l2 =>
                Node .Empty (f (some x1) none) (combine_r (.Nodes l2))
            | .Node010 x1, .Node010 x2 =>
                Node .Empty (f (some x1) (some x2)) .Empty
            | .Node010 x1, .Node011 x2 r2 =>
                Node .Empty (f (some x1) (some x2)) (combine_r (.Nodes r2))
            | .Node010 x1, .Node100 l2 =>
                Node (combine_r (.Nodes l2)) (f (some x1) none) .Empty
            | .Node010 x1, .Node101 l2 r2 =>
                Node (combine_r (.Nodes l2)) (f (some x1) none) (combine_r (.Nodes r2))
            | .Node010 x1, .Node110 l2 x2 =>
                Node (combine_r (.Nodes l2)) (f (some x1) (some x2)) .Empty
            | .Node010 x1, .Node111 l2 x2 r2 =>
                Node (combine_r (.Nodes l2)) (f (some x1) (some x2)) (combine_r (.Nodes r2))
            | .Node011 x1 r1, .Node001 l2 =>
                Node .Empty (f (some x1) none) (go r1 l2)
            | .Node011 x1 r1, .Node010 x2 =>
                Node .Empty (f (some x1) (some x2)) (combine_l (.Nodes r1))
            | .Node011 x1 r1, .Node011 x2 r2 =>
                Node .Empty (f (some x1) (some x2)) (go r1 r2)
            | .Node011 x1 r1, .Node100 l2 =>
                Node (combine_r (.Nodes l2)) (f (some x1) none) (combine_l (.Nodes r1))
            | .Node011 x1 r1, .Node101 l2 r2 =>
                Node (combine_r (.Nodes l2)) (f (some x1) none) (go r1 r2)
            | .Node011 x1 r1, .Node110 l2 x2 =>
                Node (combine_r (.Nodes l2)) (f (some x1) (some x2)) (combine_l (.Nodes r1))
            | .Node011 x1 r1, .Node111 l2 x2 r2 =>
                Node (combine_r (.Nodes l2)) (f (some x1) (some x2)) (go r1 r2)
            | .Node100 l1, .Node001 l2 =>
                Node (combine_l (.Nodes l1)) none (combine_r (.Nodes l2))
            | .Node100 l1, .Node010 x2 =>
                Node (combine_l (.Nodes l1)) (f none (some x2)) .Empty
            | .Node100 l1, .Node011 x2 r2 =>
                Node (combine_l (.Nodes l1)) (f none (some x2)) (combine_r (.Nodes r2))
            | .Node100 l1, .Node100 l2 =>
                Node (go l1 l2) none .Empty
            | .Node100 l1, .Node101 l2 r2 =>
                Node (go l1 l2) none (combine_r (.Nodes r2))
            | .Node100 l1, .Node110 l2 x2 =>
                Node (go l1 l2) (f none (some x2)) .Empty
            | .Node100 l1, .Node111 l2 x2 r2 =>
                Node (go l1 l2) (f none (some x2)) (combine_r (.Nodes r2))
            | .Node101 l1 r1, .Node001 l2 =>
                Node (combine_l (.Nodes l1)) none (go r1 l2)
            | .Node101 l1 r1, .Node010 x2 =>
                Node (combine_l (.Nodes l1)) (f none (some x2)) (combine_l (.Nodes r1))
            | .Node101 l1 r1, .Node011 x2 r2 =>
                Node (combine_l (.Nodes l1)) (f none (some x2)) (go r1 r2)
            | .Node101 l1 r1, .Node100 l2 =>
                Node (go l1 l2) none (combine_l (.Nodes r1))
            | .Node101 l1 r1, .Node101 l2 r2 =>
                Node (go l1 l2) none (go r1 r2)
            | .Node101 l1 r1, .Node110 l2 x2 =>
                Node (go l1 l2) (f none (some x2)) (combine_l (.Nodes r1))
            | .Node101 l1 r1, .Node111 l2 x2 r2 =>
                Node (go l1 l2) (f none (some x2)) (go r1 r2)
            | .Node110 l1 x1, .Node001 l2 =>
                Node (combine_l (.Nodes l1)) (f (some x1) none) (combine_r (.Nodes l2))
            | .Node110 l1 x1, .Node010 x2 =>
                Node (combine_l (.Nodes l1)) (f (some x1) (some x2)) .Empty
            | .Node110 l1 x1, .Node011 x2 r2 =>
                Node (combine_l (.Nodes l1)) (f (some x1) (some x2)) (combine_r (.Nodes r2))
            | .Node110 l1 x1, .Node100 l2 =>
                Node (go l1 l2) (f (some x1) none) .Empty
            | .Node110 l1 x1, .Node101 l2 r2 =>
                Node (go l1 l2) (f (some x1) none) (combine_r (.Nodes r2))
            | .Node110 l1 x1, .Node110 l2 x2 =>
                Node (go l1 l2) (f (some x1) (some x2)) .Empty
            | .Node110 l1 x1, .Node111 l2 x2 r2 =>
                Node (go l1 l2) (f (some x1) (some x2)) (combine_r (.Nodes r2))
            | .Node111 l1 x1 r1, .Node001 l2 =>
                Node (combine_l (.Nodes l1)) (f (some x1) none) (go r1 l2)
            | .Node111 l1 x1 r1, .Node010 x2 =>
                Node (combine_l (.Nodes l1)) (f (some x1) (some x2)) (combine_l (.Nodes r1))
            | .Node111 l1 x1 r1, .Node011 x2 r2 =>
                Node (combine_l (.Nodes l1)) (f (some x1) (some x2)) (go r1 r2)
            | .Node111 l1 x1 r1, .Node100 l2 =>
                Node (go l1 l2) (f (some x1) none) (combine_l (.Nodes r1))
            | .Node111 l1 x1 r1, .Node101 l2 r2 =>
                Node (go l1 l2) (f (some x1) none) (go r1 r2)
            | .Node111 l1 x1 r1, .Node110 l2 x2 =>
                Node (go l1 l2) (f (some x1) (some x2)) (combine_l (.Nodes r1))
            | .Node111 l1 x1 r1, .Node111 l2 x2 r2 =>
                Node (go l1 l2) (f (some x1) (some x2)) (go r1 r2)
          go a' b'

def xelements' {A : Type} : tree' A → positive → List (positive × A) → List (positive × A)
  | .Node001 r, i, k => xelements' r (.xI i) k
  | .Node010 x, i, k => (prev i, x) :: k
  | .Node011 x r, i, k => (prev i, x) :: xelements' r (.xI i) k
  | .Node100 l, i, k => xelements' l (.xO i) k
  | .Node101 l r, i, k => xelements' l (.xO i) (xelements' r (.xI i) k)
  | .Node110 l x, i, k => xelements' l (.xO i) ((prev i, x) :: k)
  | .Node111 l x r, i, k => xelements' l (.xO i) ((prev i, x) :: xelements' r (.xI i) k)

def xelements {A : Type} (m : tree A) (i : positive) : List (positive × A) :=
  match m with
  | .Empty => []
  | .Nodes m' => xelements' m' i []

def elements {A : Type} (m : tree A) : List (positive × A) := xelements m .xH

def xkeys {A : Type} (m : tree A) (i : positive) : List positive :=
  (xelements m i).map Prod.fst

def fold' {A B : Type} (f : B → positive → A → B) : positive → tree' A → B → B
  | i, .Node001 r, v => fold' f (.xI i) r v
  | i, .Node010 x, v => f v (prev i) x
  | i, .Node011 x r, v => fold' f (.xI i) r (f v (prev i) x)
  | i, .Node100 l, v => fold' f (.xO i) l v
  | i, .Node101 l r, v => fold' f (.xI i) r (fold' f (.xO i) l v)
  | i, .Node110 l x, v => f (fold' f (.xO i) l v) (prev i) x
  | i, .Node111 l x r, v => fold' f (.xI i) r (f (fold' f (.xO i) l v) (prev i) x)

def fold {A B : Type} (f : B → positive → A → B) (m : tree A) (v : B) : B :=
  match m with
  | .Empty => v
  | .Nodes m' => fold' f .xH m' v

/-! These relations are owned by `Lib.Coqlib`.  Keep source-qualified
    compatibility names here without introducing duplicate providers. -/
abbrev option_rel {A B : Type} (R : A → B → Prop) : Option A → Option B → Prop :=
  CompCert4Lean.Lib.Coqlib.option_rel R
abbrev list_norepet {A : Type} (l : List A) : Prop :=
  CompCert4Lean.Lib.Coqlib.list_norepet l
abbrev list_forall2 {A B : Type} (R : A → B → Prop) : List A → List B → Prop :=
  CompCert4Lean.Lib.Coqlib.list_forall2 R

def gemptyStatement : Prop := ∀ (A : Type) (i : positive), get i (empty A) = none
def gss0Statement : Prop := ∀ {A : Type} (p : positive) (x : A), get' p (set0 p x) = some x
def gso0Statement : Prop := ∀ {A : Type} {p q : positive} (x : A), p ≠ q → get' p (set0 q x) = none
def gssStatement : Prop := ∀ {A : Type} (i : positive) (x : A) (m : tree A), get i (set i x m) = some x
def gsoStatement : Prop := ∀ {A : Type} {i j : positive} (x : A) (m : tree A), i ≠ j → get i (set j x m) = get i m
def gsspecStatement : Prop := ∀ {A : Type} (i j : positive) (x : A) (m : t A),
  get i (set j x m) = match peq i j with | .left _ => some x | .right _ => get i m
def gNodeStatement : Prop := ∀ {A : Type} (i : positive) (l : tree A) (x : Option A) (r : tree A),
  get i (Node l x r) = match i with | .xH => x | .xO j => get j l | .xI j => get j r
def grsStatement : Prop := ∀ {A : Type} (i : positive) (m : tree A), get i (remove i m) = none
def groStatement : Prop := ∀ {A : Type} {i j : positive} (m : tree A), i ≠ j → get i (remove j m) = get i m
def grspecStatement : Prop := ∀ {A : Type} (i j : elt) (m : t A),
  get i (remove j m) = match elt_eq i j with | .left _ => none | .right _ => get i m

def unroll_tree_recStatement : Prop :=
  ∀ {A B : Type} (emptyCase : B)
    (node : tree A → B → Option A → tree A → B → B)
    (l : tree A) (o : Option A) (r : tree A),
    not_trivially_empty l o r →
    tree_rec emptyCase node (Node l o r) = node l (tree_rec emptyCase node l) o r (tree_rec emptyCase node r)
def unroll_tree_rec2_NEStatement : Prop :=
  ∀ {A B C : Type} (base : C) (base1 : tree B → C) (base2 : tree A → C)
    (nodes : tree A → Option A → tree A → tree B → Option B → tree B → C → C → C)
    (l1 : tree A) (o1 : Option A) (r1 : tree A),
    not_trivially_empty l1 o1 r1 →
    tree_rec2 base base1 base2 nodes (Node l1 o1 r1) .Empty = base2 (Node l1 o1 r1)
def unroll_tree_rec2_ENStatement : Prop :=
  ∀ {A B C : Type} (base : C) (base1 : tree B → C) (base2 : tree A → C)
    (nodes : tree A → Option A → tree A → tree B → Option B → tree B → C → C → C)
    (l2 : tree B) (o2 : Option B) (r2 : tree B),
    not_trivially_empty l2 o2 r2 →
    tree_rec2 base base1 base2 nodes .Empty (Node l2 o2 r2) = base1 (Node l2 o2 r2)
def unroll_tree_rec2_NNStatement : Prop :=
  ∀ {A B C : Type} (base : C) (base1 : tree B → C) (base2 : tree A → C)
    (nodes : tree A → Option A → tree A → tree B → Option B → tree B → C → C → C)
    (l1 : tree A) (o1 : Option A) (r1 : tree A) (l2 : tree B) (o2 : Option B) (r2 : tree B),
    not_trivially_empty l1 o1 r1 → not_trivially_empty l2 o2 r2 →
    tree_rec2 base base1 base2 nodes (Node l1 o1 r1) (Node l2 o2 r2) =
      nodes l1 o1 r1 l2 o2 r2
        (tree_rec2 base base1 base2 nodes l1 l2)
        (tree_rec2 base base1 base2 nodes r1 r2)

def tree'_not_emptyStatement : Prop := ∀ {A : Type} (m : tree' A), ∃ i, get' i m ≠ none
def extensionality_emptyStatement : Prop := ∀ {A : Type} (m : tree A), (∀ i, get i m = none) → m = .Empty
def extensionalityStatement : Prop := ∀ {A : Type} (m1 m2 : tree A), (∀ i, get i m1 = get i m2) → m1 = m2
def gsidentStatement : Prop := ∀ {A : Type} (i : positive) (m : t A) {v : A}, get i m = some v → set i v m = m
def set2Statement : Prop := ∀ {A : Type} (i : elt) (m : t A) (v1 v2 : A), set i v2 (set i v1 m) = set i v2 m

def prev_append_prevStatement : Prop := ∀ (i j : positive), prev (prev_append i j) = prev_append j i
def prev_involutiveStatement : Prop := ∀ (i : positive), prev (prev i) = i
def prev_append_injStatement : Prop := ∀ (i j j' : positive), prev_append i j = prev_append i j' → j = j'
def gmap'Statement : Prop := ∀ {A B : Type} (f : positive → A → B) (i j : positive) (m : tree' A),
  get' i (map' f m j) = Option.map (f (prev (prev_append i j))) (get' i m)
def gmapStatement : Prop := ∀ {A B : Type} (f : positive → A → B) (i : positive) (m : t A),
  get i (map f m) = Option.map (f i) (get i m)
def gmap1Statement : Prop := ∀ {A B : Type} (f : A → B) (i : elt) (m : t A),
  get i (map1 f m) = Option.map f (get i m)
def gmap_filter1Statement : Prop := ∀ {A B : Type} (f : A → Option B) (m : tree A) (i : positive),
  get i (map_filter1 f m) = match get i m with | none => none | some a => f a
def gcombine_lStatement : Prop := ∀ {A B C : Type} (f : Option A → Option B → Option C)
  (f_none_none : f none none = none) (m : tree A) (i : positive),
  get i (map_filter1 (fun a => f (some a) none) m) = f (get i m) none
def gcombine_rStatement : Prop := ∀ {A B C : Type} (f : Option A → Option B → Option C)
  (f_none_none : f none none = none) (m : tree B) (i : positive),
  get i (map_filter1 (fun b => f none (some b)) m) = f none (get i m)
def gcombineStatement : Prop := ∀ {A B C : Type} (f : Option A → Option B → Option C)
  (f_none_none : f none none = none) (m1 : t A) (m2 : t B) (i : positive),
  get i (combine f m1 m2) = f (get i m1) (get i m2)

def xelements'_appendStatement : Prop := ∀ {A : Type} (m : tree' A) (i : positive) (k1 k2 : List (positive × A)),
  xelements' m i (k1 ++ k2) = xelements' m i k1 ++ k2
def xelements_NodeStatement : Prop := ∀ {A : Type} (l : tree A) (o : Option A) (r : tree A) (i : positive),
  xelements (Node l o r) i = xelements l (.xO i) ++ (match o with | none => [] | some v => [(prev i, v)]) ++ xelements r (.xI i)
def xelements_correctStatement : Prop := ∀ {A : Type} (m : tree A) (i j : positive) {v : A},
  get i m = some v → (prev (prev_append i j), v) ∈ xelements m j
def elements_correctStatement : Prop := ∀ {A : Type} (m : t A) (i : positive) {v : A},
  get i m = some v → (i, v) ∈ elements m
def in_xelementsStatement : Prop := ∀ {A : Type} (m : tree A) (i k : positive) (v : A),
  (k, v) ∈ xelements m i → ∃ j, k = prev (prev_append j i) ∧ get j m = some v
def elements_completeStatement : Prop := ∀ {A : Type} (m : t A) (i : positive) (v : A),
  (i, v) ∈ elements m → get i m = some v
def xkeys_NodeStatement : Prop := ∀ {A : Type} (m1 : t A) (o : Option A) (m2 : t A) (i : positive),
  xkeys (Node m1 o m2) i = xkeys m1 (.xO i) ++ (match o with | none => [] | some v => [prev i]) ++ xkeys m2 (.xI i)
def in_xkeysStatement : Prop := ∀ {A : Type} (m : t A) (i k : positive), k ∈ xkeys m i → ∃ j, k = prev (prev_append j i)
def xelements_keys_norepetStatement : Prop := ∀ {A : Type} (m : t A) (i : positive), list_norepet (xkeys m i)
def elements_keys_norepetStatement : Prop := ∀ {A : Type} (m : t A), list_norepet ((elements m).map Prod.fst)
def elements_canonical_order'Statement : Prop := ∀ {A B : Type} (R : A → B → Prop) (m : t A) (n : t B),
  (∀ i, option_rel R (get i m) (get i n)) →
  list_forall2 (fun p q => p.1 = q.1 ∧ R p.2 q.2) (elements m) (elements n)
def elements_canonical_orderStatement : Prop := ∀ {A B : Type} (R : A → B → Prop) (m : t A) (n : t B),
  (∀ i x, get i m = some x → ∃ y, get i n = some y ∧ R x y) →
  (∀ i y, get i n = some y → ∃ x, get i m = some x ∧ R x y) →
  list_forall2 (fun p q => p.1 = q.1 ∧ R p.2 q.2) (elements m) (elements n)
def fold'_xelements'Statement : Prop := ∀ {A B : Type} (f : B → positive → A → B) (m : tree' A)
  (i : positive) (v : B) (l : List (positive × A)),
  List.foldl (fun a p => f a p.1 p.2) (fold' f i m v) l =
    List.foldl (fun a p => f a p.1 p.2) v (xelements' m i l)
def fold_specStatement : Prop := ∀ {A B : Type} (f : B → positive → A → B) (v : B) (m : t A),
  fold f m v = List.foldl (fun a p => f a p.1 p.2) v (elements m)

private theorem getSet0_proof (A : Type) (x y : positive) (v : A) :
    get' x (set0 y v) = if h : x = y then some v else none := by
  induction x generalizing y with
  | xH =>
      cases y <;> simp [set0, get']
  | xO x ih =>
      cases y with
      | xH => simp [set0, get']
      | xO y => simp [set0, get', ih]
      | xI y => simp [set0, get']
  | xI x ih =>
      cases y with
      | xH => simp [set0, get']
      | xO y => simp [set0, get']
      | xI y => simp [set0, get', ih]

private theorem getSet'_proof (A : Type) (x y : positive) (v : A)
    (m : tree' A) :
    get' x (set' y v m) = if h : x = y then some v else get' x m := by
  induction x generalizing y m with
  | xH =>
      cases y <;> cases m <;> simp [set', get']
  | xO x ih =>
      cases y with
      | xH => cases m <;> simp [set', get']
      | xO y => cases m <;> simp [set', get', ih, getSet0_proof]
      | xI y => cases m <;> simp [set', get', getSet0_proof]
  | xI x ih =>
      cases y with
      | xH => cases m <;> simp [set', get']
      | xO y => cases m <;> simp [set', get', getSet0_proof]
      | xI y => cases m <;> simp [set', get', ih, getSet0_proof]

private theorem getSet_proof (A : Type) (x y : positive) (v : A)
    (m : tree A) :
    get x (set y v m) = if h : x = y then some v else get x m := by
  cases m with
  | Empty => simpa [get, set] using getSet0_proof A x y v
  | Nodes m => simpa [get, set] using getSet'_proof A x y v m

theorem gsspec_proof : gsspecStatement := by
  intro A i j x m
  cases h : peq i j with
  | left hij =>
      subst j
      simpa [h] using (getSet_proof A i i x m)
  | right hne =>
      simpa [h, hne] using (getSet_proof A i j x m)

theorem getSet_equation {A : Type} (i j : positive) (x : A) (m : tree A) :
    get i (set j x m) = if h : i = j then some x else get i m :=
  getSet_proof A i j x m

private theorem getNode_equation {A : Type} (i : positive) (l : tree A)
    (o : Option A) (r : tree A) :
    get i (Node l o r) = match i with
      | .xH => o
      | .xO j => get j l
      | .xI j => get j r := by
  cases i <;> cases l <;> cases o <;> cases r <;> rfl

private theorem getNodes_equation {A : Type} (i : positive) (m : tree' A) :
    get i (Nodes m) = get' i m := rfl

private theorem getEmpty_equation {A : Type} (i : positive) :
    get i (Empty : tree A) = none := rfl

theorem unroll_tree_rec2_NE_proof : unroll_tree_rec2_NEStatement := by
  intro A B C base base1 base2 nodes l1 o1 r1 hne
  cases l1 <;> cases o1 <;> cases r1 <;>
    simp_all [not_trivially_empty, Node, tree_rec2, tree_rec2']

theorem unroll_tree_rec2_EN_proof : unroll_tree_rec2_ENStatement := by
  intro A B C base base1 base2 nodes l2 o2 r2 hne
  cases l2 <;> cases o2 <;> cases r2 <;>
    simp_all [not_trivially_empty, Node, tree_rec2, tree_rec2']

theorem unroll_tree_rec2_NN_proof : unroll_tree_rec2_NNStatement := by
  intro A B C base base1 base2 nodes l1 o1 r1 l2 o2 r2 hne1 hne2
  cases l1 <;> cases o1 <;> cases r1 <;>
    cases l2 <;> cases o2 <;> cases r2 <;>
      simp_all [not_trivially_empty, Node, tree_rec2, tree_rec2']

private theorem get_map_filter1_nodes_proof {A B : Type} (f : A → Option B)
    (m : tree' A) (i : positive) :
    get i (map_filter1.go f m) = Option.bind (get' i m) f := by
  induction m generalizing i with
  | Node001 r ih =>
      cases i with
      | xH => cases h : map_filter1.go f r <;>
          simp [map_filter1, map_filter1.go, h, get, get', Option.bind]
      | xO q => cases h : map_filter1.go f r <;>
          simp [map_filter1, map_filter1.go, h, get, get', Option.bind]
      | xI q => cases h : map_filter1.go f r <;>
          simpa [map_filter1.go, h, get, get', Option.bind] using ih q
  | Node010 x =>
      cases i <;> cases h : f x <;>
        simp [map_filter1, map_filter1.go, h, get, get', Option.bind]
  | Node011 x r ih =>
      cases i with
      | xH => cases hf : f x <;> cases hr : map_filter1.go f r <;>
          simp [map_filter1, map_filter1.go, hf, hr, get, get', Option.bind]
      | xO q => cases hf : f x <;> cases hr : map_filter1.go f r <;>
          simp [map_filter1, map_filter1.go, hf, hr, get, get', Option.bind]
      | xI q => cases hf : f x <;> cases hr : map_filter1.go f r <;>
          simpa [map_filter1.go, hf, hr, get, get', Option.bind] using ih q
  | Node100 l ih =>
      cases i with
      | xH => cases h : map_filter1.go f l <;>
          simp [map_filter1, map_filter1.go, h, get, get', Option.bind]
      | xO q => cases h : map_filter1.go f l <;>
          simpa [map_filter1.go, h, get, get', Option.bind] using ih q
      | xI q => cases h : map_filter1.go f l <;>
          simp [map_filter1, map_filter1.go, h, get, get', Option.bind]
  | Node101 l r ihl ihr =>
      cases i with
      | xH => cases hl : map_filter1.go f l <;> cases hr : map_filter1.go f r <;>
          simp [map_filter1, map_filter1.go, hl, hr, get, get', Option.bind]
      | xO q => cases hl : map_filter1.go f l <;> cases hr : map_filter1.go f r <;>
          simpa [map_filter1.go, hl, hr, get, get', Option.bind] using ihl q
      | xI q => cases hl : map_filter1.go f l <;> cases hr : map_filter1.go f r <;>
          simpa [map_filter1.go, hl, hr, get, get', Option.bind] using ihr q
  | Node110 l x ih =>
      cases i with
      | xH => cases hl : map_filter1.go f l <;> cases hf : f x <;>
          simp [map_filter1, map_filter1.go, hl, hf, get, get', Option.bind]
      | xO q => cases hl : map_filter1.go f l <;> cases hf : f x <;>
          simpa [map_filter1.go, hl, hf, get, get', Option.bind] using ih q
      | xI q => cases hl : map_filter1.go f l <;> cases hf : f x <;>
          simp [map_filter1, map_filter1.go, hl, hf, get, get', Option.bind]
  | Node111 l x r ihl ihr =>
      cases i with
      | xH => cases hl : map_filter1.go f l <;> cases hf : f x <;>
          cases hr : map_filter1.go f r <;>
          simp [map_filter1, map_filter1.go, hl, hf, hr, get, get', Option.bind]
      | xO q => cases hl : map_filter1.go f l <;> cases hf : f x <;>
          cases hr : map_filter1.go f r <;>
          simpa [map_filter1.go, hl, hf, hr, get, get', Option.bind] using ihl q
      | xI q => cases hl : map_filter1.go f l <;> cases hf : f x <;>
          cases hr : map_filter1.go f r <;>
          simpa [map_filter1.go, hl, hf, hr, get, get', Option.bind] using ihr q

private theorem get_map_filter1_proof {A B : Type} (f : A → Option B)
    (m : tree A) (i : positive) :
    get i (map_filter1 f m) = Option.bind (get i m) f := by
  cases m with
  | Empty => rfl
  | Nodes m => simpa [map_filter1, get] using get_map_filter1_nodes_proof f m i

theorem gcombine_l_proof : gcombine_lStatement := by
  intro A B C f hnone m i
  rw [get_map_filter1_proof]
  cases hget : get i m <;> simp [Option.bind, hget, hnone]

theorem gcombine_r_proof : gcombine_rStatement := by
  intro A B C f hnone m i
  rw [get_map_filter1_proof]
  cases hget : get i m <;> simp [Option.bind, hget, hnone]

private theorem get_combine_go_proof {A B C : Type}
    (f : Option A → Option B → Option C) (hnone : f none none = none)
    (a : tree' A) (b : tree' B) (i : positive) :
    get i (combine.go f (map_filter1 (fun x => f (some x) none))
      (map_filter1 (fun x => f none (some x))) a b) =
      f (get i (.Nodes a)) (get i (.Nodes b)) := by
  induction a generalizing b i with
  | Node001 l ih =>
      cases b <;> cases i <;>
        simp_all [combine.go, get', getNode_equation, getNodes_equation, getEmpty_equation,
          get_map_filter1_proof, Option.bind, hnone] <;>
        try cases h : get' _ _ <;> simp_all [Option.bind, h, hnone]
  | Node010 x =>
      cases b <;> cases i <;>
        simp_all [combine.go, get', getNode_equation, getNodes_equation, getEmpty_equation,
          get_map_filter1_proof, Option.bind, hnone] <;>
        try cases h : get' _ _ <;> simp_all [Option.bind, h, hnone]
  | Node011 x r ih =>
      cases b <;> cases i <;>
        simp_all [combine.go, get', getNode_equation, getNodes_equation, getEmpty_equation,
          get_map_filter1_proof, Option.bind, hnone] <;>
        try cases h : get' _ _ <;> simp_all [Option.bind, h, hnone]
  | Node100 l ih =>
      cases b <;> cases i <;>
        simp_all [combine.go, get', getNode_equation, getNodes_equation, getEmpty_equation,
          get_map_filter1_proof, Option.bind, hnone] <;>
        try cases h : get' _ _ <;> simp_all [Option.bind, h, hnone]
  | Node101 l r ihl ihr =>
      cases b <;> cases i <;>
        simp_all [combine.go, get', getNode_equation, getNodes_equation, getEmpty_equation,
          get_map_filter1_proof, Option.bind, hnone] <;>
        try cases h : get' _ _ <;> simp_all [Option.bind, h, hnone]
  | Node110 l x ih =>
      cases b <;> cases i <;>
        simp_all [combine.go, get', getNode_equation, getNodes_equation, getEmpty_equation,
          get_map_filter1_proof, Option.bind, hnone] <;>
        try cases h : get' _ _ <;> simp_all [Option.bind, h, hnone]
  | Node111 l x r ihl ihr =>
      cases b <;> cases i <;>
        simp_all [combine.go, get', getNode_equation, getNodes_equation, getEmpty_equation,
          get_map_filter1_proof, Option.bind, hnone] <;>
        try cases h : get' _ _ <;> simp_all [Option.bind, h, hnone]

theorem gcombine_proof : gcombineStatement := by
  intro A B C f hnone m1 m2 i
  cases m1 with
  | Empty =>
      cases m2 with
      | Empty => simp [combine, get, hnone]
      | Nodes b =>
          simpa [combine, get] using
            (gcombine_r_proof f hnone (.Nodes b) i)
  | Nodes a =>
      cases m2 with
      | Empty =>
          simpa [combine, get] using
            (gcombine_l_proof f hnone (.Nodes a) i)
      | Nodes b =>
          simpa [combine, get] using get_combine_go_proof f hnone a b i

theorem gNode_proof : gNodeStatement := by
  intro A i l o r
  cases i <;> cases l <;> cases o <;> cases r <;> rfl

private theorem getRemove'_proof {A : Type} (x y : positive) (m : tree' A) :
    get x (remove' y m) = if h : x = y then none else get' x m := by
  induction y generalizing x m with
  | xH =>
      cases x <;> cases m <;>
        simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
  | xO q ih =>
      cases x with
      | xH =>
          cases m with
          | Node001 r => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node010 y => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node011 y r => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node100 l => cases h : remove' q l <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node101 l r => cases h : remove' q l <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node110 l y => cases h : remove' q l <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node111 l y r => cases h : remove' q l <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
      | xO p =>
          cases m with
          | Node001 r => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node010 y => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node011 y r => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node100 l => cases h : remove' q l <;>
              simpa [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation] using ih p l
          | Node101 l r => cases h : remove' q l <;>
              simpa [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation] using ih p l
          | Node110 l y => cases h : remove' q l <;>
              simpa [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation] using ih p l
          | Node111 l y r => cases h : remove' q l <;>
              simpa [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation] using ih p l
      | xI p =>
          cases m with
          | Node001 r => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node010 y => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node011 y r => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node100 l => cases h : remove' q l <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node101 l r => cases h : remove' q l <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node110 l y => cases h : remove' q l <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node111 l y r => cases h : remove' q l <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
  | xI q ih =>
      cases x with
      | xH =>
          cases m with
          | Node001 r => cases h : remove' q r <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node010 y => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node011 y r => cases h : remove' q r <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node100 l => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node101 l r => cases h : remove' q r <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node110 l y => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node111 l y r => cases h : remove' q r <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
      | xO p =>
          cases m with
          | Node001 r => cases h : remove' q r <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node010 y => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node011 y r => cases h : remove' q r <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node100 l => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node101 l r => cases h : remove' q r <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node110 l y => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node111 l y r => cases h : remove' q r <;>
              simp [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation]
      | xI p =>
          cases m with
          | Node001 r => cases h : remove' q r <;>
              simpa [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation] using ih p r
          | Node010 y => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node011 y r => cases h : remove' q r <;>
              simpa [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation] using ih p r
          | Node100 l => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node101 l r => cases h : remove' q r <;>
              simpa [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation] using ih p r
          | Node110 l y => simp [remove', get', getNode_equation, getNodes_equation, getEmpty_equation]
          | Node111 l y r => cases h : remove' q r <;>
              simpa [remove', h, get', getNode_equation, getNodes_equation, getEmpty_equation] using ih p r

private theorem getRemove_proof {A : Type} (x y : positive) (m : tree A) :
    get x (remove y m) = if h : x = y then none else get x m := by
  cases m with
  | Empty => simp [remove, get]
  | Nodes m => exact getRemove'_proof x y m

theorem getRemove_equation {A : Type} (x y : positive) (m : tree A) :
    get x (remove y m) = if h : x = y then none else get x m :=
  getRemove_proof x y m

theorem grspec_proof : grspecStatement := by
  intro A i j m
  unfold elt at i j ⊢
  change get i (remove j m) = _
  cases h : peq i j with
  | left hij =>
      subst j
      have hremove : get i (remove i m) = none := by
        calc
          get i (remove i m) = if h : i = i then none else get i m :=
            getRemove_proof (A := A) i i m
          _ = none := by simp
      simpa [elt_eq, h] using hremove
  | right hne =>
      have hremove : get i (remove j m) = get i m := by
        simpa [hne] using (getRemove_proof (A := A) i j m)
      simpa [elt_eq, h, hne] using hremove

theorem grs_proof : grsStatement := by
  intro A i m
  simpa using getRemove_proof i i m

theorem gro_proof : groStatement := by
  intro A i j m h
  simpa [h] using getRemove_proof i j m

private theorem foldl_step (g : B → (positive × A) → B) (a : B)
    (p : positive × A) (l : List (positive × A)) :
    List.foldl g (g a p) l = List.foldl g a (p :: l) := by
  induction l generalizing a with
  | nil => rfl
  | cons q l ih => simp [List.foldl, ih]

private theorem foldl_step' {A B : Type} (f : B → positive → A → B)
    (a : B) (k : positive) (v : A) (l : List (positive × A)) :
    List.foldl (fun a p => f a p.1 p.2) (f a k v) l =
      List.foldl (fun a p => f a p.1 p.2) a ((k, v) :: l) := by
  induction l generalizing a with
  | nil => rfl
  | cons q l ih => simp [List.foldl, ih]

private theorem fold'_xelements'_proof : fold'_xelements'Statement := by
  intro A B f m i v l
  induction m generalizing i v l <;>
    simp_all [fold', xelements', List.foldl, List.foldl_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals rw [foldl_step']
  all_goals simp_all [List.foldl_append]

theorem fold_spec_proof : fold_specStatement := by
  intro A B f v m
  cases m with
  | Empty => rfl
  | Nodes m =>
      simpa [fold, elements, xelements, fold'_xelements'Statement] using
        (fold'_xelements'_proof (A := A) (B := B) f m .xH v [])

private theorem prev_append_xI (i j : positive) :
    prev (prev_append i (xI j)) = prev (prev_append (xI i) j) := by
  induction i with
  | xH => rfl
  | xI i ih => simp [prev, prev_append, ih]
  | xO i ih => simp [prev, prev_append, ih]

private theorem prev_append_xO (i j : positive) :
    prev (prev_append i (xO j)) = prev (prev_append (xO i) j) := by
  induction i with
  | xH => rfl
  | xI i ih => simp [prev, prev_append, ih]
  | xO i ih => simp [prev, prev_append, ih]

private theorem mem_suffix_xelements' {A : Type} (m : tree' A) (i : positive)
    (suffix : List (positive × A)) (p : positive × A) :
    p ∈ suffix → p ∈ xelements' m i suffix := by
  induction m generalizing i suffix p with
  | Node001 r ih => exact ih (xI i) suffix p
  | Node010 x =>
      intro h
      exact List.mem_cons_of_mem _ h
  | Node011 x r ih =>
      intro h
      exact List.mem_cons_of_mem _ (ih (xI i) suffix p h)
  | Node100 l ih => exact ih (xO i) suffix p
  | Node101 l r ihl ihr =>
      intro h
      have hr : p ∈ xelements' r (xI i) suffix :=
        ihr (xI i) suffix p h
      exact ihl (xO i) (xelements' r (xI i) suffix) p (by
        simp [hr])
  | Node110 l x ih =>
      intro h
      exact ih (xO i) ((prev i, x) :: suffix) p (List.mem_cons_of_mem _ h)
  | Node111 l x r ihl ihr =>
      intro h
      have hr : p ∈ xelements' r (xI i) suffix :=
        ihr (xI i) suffix p h
      exact ihl (xO i) ((prev i, x) :: xelements' r (xI i) suffix) p (by
        simp [hr])

private theorem get_xelements'_correct {A : Type} (m : tree' A) (i j : positive)
    (v : A) (suffix : List (positive × A)) :
    get' i m = some v →
      (prev (prev_append i j), v) ∈ xelements' m j suffix := by
  induction m generalizing i j suffix with
  | Node001 r ih =>
      cases i with
      | xH => simp [get']
      | xO q => simp [get']
      | xI q =>
          intro h
          simpa [get', xelements', prev_append_xI] using (ih q (xI j) suffix h)
  | Node010 x =>
      cases i with
      | xH =>
          intro h
          cases h
          simp [xelements', prev_append]
      | xO q => simp [get']
      | xI q => simp [get']
  | Node011 x r ih =>
      cases i with
      | xH =>
          intro h
          cases h
          simp [xelements', prev_append]
      | xO q => simp [get']
      | xI q =>
          intro h
          have hp : (prev (prev_append (xI q) j), v) ∈
              xelements' r (xI j) suffix := by
            simpa [prev_append_xI] using (ih q (xI j) suffix h)
          exact List.mem_cons_of_mem (prev j, x) hp
  | Node100 l ih =>
      cases i with
      | xH => simp [get']
      | xO q =>
          intro h
          simpa [get', xelements', prev_append_xO] using (ih q (xO j) suffix h)
      | xI q => simp [get']
  | Node101 l r ihl ihr =>
      cases i with
      | xH => simp [get']
      | xO q =>
          intro h
          simpa [get', xelements', prev_append_xO] using
            (ihl q (xO j) (xelements' r (xI j) suffix) h)
      | xI q =>
          intro h
          have hp := ihr q (xI j) suffix h
          exact mem_suffix_xelements' l (xO j) (xelements' r (xI j) suffix) _
            (by simpa [get', xelements', prev_append_xI] using hp)
  | Node110 l x ih =>
      cases i with
      | xH =>
          intro h
          have hv : x = v := Option.some.inj h
          subst v
          exact mem_suffix_xelements' l (xO j) ((prev j, x) :: suffix) (prev j, x) (by simp)
      | xO q =>
          intro h
          simpa [get', xelements', prev_append_xO] using
            (ih q (xO j) ((prev j, x) :: suffix) h)
      | xI q => simp [get']
  | Node111 l x r ihl ihr =>
      cases i with
      | xH =>
          intro h
          have hv : x = v := Option.some.inj h
          subst v
          exact mem_suffix_xelements' l (xO j)
            ((prev j, x) :: xelements' r (xI j) suffix) (prev j, x) (by simp)
      | xO q =>
          intro h
          simpa [get', xelements', prev_append_xO] using
            (ihl q (xO j) ((prev j, x) :: xelements' r (xI j) suffix) h)
      | xI q =>
          intro h
          have hp : (prev (prev_append (xI q) j), v) ∈
              xelements' r (xI j) suffix := by
            simpa [prev_append_xI] using (ihr q (xI j) suffix h)
          exact mem_suffix_xelements' l (xO j)
            ((prev j, x) :: xelements' r (xI j) suffix)
            (prev (prev_append (xI q) j), v) (by simp [hp])


private theorem prev_append_swap (i j : positive) :
    prev (prev_append i j) = prev_append j i := by
  induction i generalizing j with
  | xH => rfl
  | xI i ih =>
      change prev (prev_append i (xI j)) = prev_append j (xI i)
      rw [ih (xI j)]
      rfl
  | xO i ih =>
      change prev (prev_append i (xO j)) = prev_append j (xO i)
      rw [ih (xO j)]
      rfl

private theorem prev_involutive (i : positive) : prev (prev i) = i := by
  have h := prev_append_swap i xH
  simpa [prev, prev_append] using h

theorem elements_correct_proof : elements_correctStatement := by
  intro A m i v h
  cases m with
  | Empty => simp [elements, xelements, get] at h
  | Nodes m =>
      have h' : get' i m = some v := by simpa [get] using h
      have hc := get_xelements'_correct m i .xH v [] h'
      have hkey : prev (prev_append i xH) = i := by
        change prev (prev i) = i
        exact prev_involutive i
      simpa [elements, xelements, hkey] using hc

private theorem xelements'_append_equation {A : Type} (m : tree' A) (i : positive)
    (k1 k2 : List (positive × A)) :
    xelements' m i (k1 ++ k2) = xelements' m i k1 ++ k2 := by
  induction m generalizing i k1 k2 with
  | Node001 r ih => exact ih (xI i) k1 k2
  | Node010 x => simp [xelements']
  | Node011 x r ih => simp [xelements', ih, List.append_assoc]
  | Node100 l ih => exact ih (xO i) k1 k2
  | Node101 l r ihl ihr =>
      simp [xelements', ihl, ihr, List.append_assoc]
  | Node110 l x ih =>
      change xelements' l (xO i) ((prev i, x) :: (k1 ++ k2)) =
        xelements' l (xO i) ((prev i, x) :: k1) ++ k2
      exact ih (xO i) ((prev i, x) :: k1) k2
  | Node111 l x r ihl ihr =>
      simp only [xelements']
      rw [ihr (xI i) k1 k2]
      exact ihl (xO i) ((prev i, x) :: xelements' r (xI i) k1) k2

private theorem in_xelements'_complete {A : Type} (m : tree' A) (i : positive)
    (p : positive × A) :
    p ∈ xelements' m i [] →
      ∃ j, p.1 = prev (prev_append j i) ∧ get' j m = some p.2 := by
  induction m generalizing i p with
  | Node001 r ih =>
      intro h
      have hr := ih (xI i) p (by simpa [xelements'] using h)
      rcases hr with ⟨j, hj, hget⟩
      refine ⟨xI j, ?_, ?_⟩
      · simpa [prev_append] using hj
      · simpa [get'] using hget
  | Node010 x =>
      intro h
      rcases p with ⟨k, v⟩
      simp [xelements'] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨xH, by simp [prev_append], by simp [get']⟩
  | Node011 x r ih =>
      intro h
      rcases p with ⟨k, v⟩
      simp [xelements'] at h
      rcases h with h | h
      · have hp : (k, v) = (prev i, x) := by simpa using h
        rcases hp with ⟨rfl, rfl⟩
        exact ⟨xH, by simp [prev_append], by simp [get']⟩
      · have hr := ih (xI i) (k, v) h
        rcases hr with ⟨j, hj, hget⟩
        refine ⟨xI j, ?_, ?_⟩
        · simpa [prev_append] using hj
        · simpa [get'] using hget
  | Node100 l ih =>
      intro h
      have hl := ih (xO i) p (by simpa [xelements'] using h)
      rcases hl with ⟨j, hj, hget⟩
      refine ⟨xO j, ?_, ?_⟩
      · simpa [prev_append] using hj
      · simpa [get'] using hget
  | Node101 l r ihl ihr =>
      intro h
      change p ∈ xelements' l (xO i) (xelements' r (xI i) []) at h
      have hsplit : xelements' l (xO i) (xelements' r (xI i) []) =
          xelements' l (xO i) [] ++ xelements' r (xI i) [] := by
        simpa using (xelements'_append_equation l (xO i) [] (xelements' r (xI i) []))
      rw [hsplit] at h
      simp only [List.mem_append] at h
      rcases h with h | h
      · have hl := ihl (xO i) p h
        rcases hl with ⟨j, hj, hget⟩
        refine ⟨xO j, ?_, ?_⟩
        · simpa [prev_append] using hj
        · simpa [get'] using hget
      · have hr := ihr (xI i) p h
        rcases hr with ⟨j, hj, hget⟩
        refine ⟨xI j, ?_, ?_⟩
        · simpa [prev_append] using hj
        · simpa [get'] using hget
  | Node110 l x ih =>
      intro h
      rcases p with ⟨k, v⟩
      change (k, v) ∈ xelements' l (xO i) [(prev i, x)] at h
      have hsplit : xelements' l (xO i) [(prev i, x)] =
          xelements' l (xO i) [] ++ [(prev i, x)] := by
        simpa using (xelements'_append_equation l (xO i) [] [(prev i, x)])
      rw [hsplit] at h
      simp only [List.mem_append] at h
      rcases h with h | h
      · have hl := ih (xO i) (k, v) h
        rcases hl with ⟨j, hj, hget⟩
        refine ⟨xO j, ?_, ?_⟩
        · simpa [prev_append] using hj
        · simpa [get'] using hget
      · have hp : (k, v) = (prev i, x) := by simpa using h
        rcases hp with ⟨rfl, rfl⟩
        exact ⟨xH, by simp [prev_append], by simp [get']⟩
  | Node111 l x r ihl ihr =>
      intro h
      rcases p with ⟨k, v⟩
      change (k, v) ∈ xelements' l (xO i)
        ((prev i, x) :: xelements' r (xI i) []) at h
      have hsplit : xelements' l (xO i)
          ((prev i, x) :: xelements' r (xI i) []) =
          xelements' l (xO i) [] ++
            ((prev i, x) :: xelements' r (xI i) []) := by
        simpa using (xelements'_append_equation l (xO i) []
          ((prev i, x) :: xelements' r (xI i) []))
      rw [hsplit] at h
      simp only [List.mem_append] at h
      rcases h with h | h
      · have hl := ihl (xO i) (k, v) h
        rcases hl with ⟨j, hj, hget⟩
        refine ⟨xO j, ?_, ?_⟩
        · simpa [prev_append] using hj
        · simpa [get'] using hget
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · have hp : (k, v) = (prev i, x) := by simpa using h
          rcases hp with ⟨rfl, rfl⟩
          exact ⟨xH, by simp [prev_append], by simp [get']⟩
        · have hr := ihr (xI i) (k, v) h
          rcases hr with ⟨j, hj, hget⟩
          refine ⟨xI j, ?_, ?_⟩
          · simpa [prev_append] using hj
          · simpa [get'] using hget

private theorem prev_append_injective (i : positive) :
    Function.Injective (prev_append i) := by
  induction i with
  | xH => intro j k h; exact h
  | xI i ih =>
      intro j k h
      have h' : xI j = xI k := ih h
      cases h'
      rfl
  | xO i ih =>
      intro j k h
      have h' : xO j = xO k := ih h
      cases h'
      rfl

private theorem key_form_xelements' {A : Type} (m : tree' A) (i : positive)
    (p : positive × A) (h : p ∈ xelements' m i []) :
    ∃ j, p.1 = prev_append i j := by
  rcases in_xelements'_complete m i p h with ⟨j, hj, _⟩
  exact ⟨j, by simpa [prev_append_swap] using hj⟩

private theorem keys_disjoint_xO_xI {A B : Type} (l : tree' A) (r : tree' B)
    (i : positive) :
    ∀ k, k ∈ (xelements' l (xO i) []).map Prod.fst →
      k ∉ (xelements' r (xI i) []).map Prod.fst := by
  intro k hl hr
  rcases List.mem_map.mp hl with ⟨p, hp, rfl⟩
  rcases List.mem_map.mp hr with ⟨q, hq, hkey⟩
  rcases key_form_xelements' l (xO i) p hp with ⟨j, hj⟩
  rcases key_form_xelements' r (xI i) q hq with ⟨k, hk⟩
  have heq : prev_append i (xO j) = prev_append i (xI k) := by
    calc
      prev_append i (xO j) = p.1 := by simpa [prev_append] using hj.symm
      _ = q.1 := hkey.symm
      _ = prev_append i (xI k) := by simpa [prev_append] using hk
  have hbits : xO j = xI k := prev_append_injective i heq
  cases hbits

private theorem key_not_in_xO {A : Type} (l : tree' A) (i : positive) :
    prev i ∉ (xelements' l (xO i) []).map Prod.fst := by
  intro h
  rcases List.mem_map.mp h with ⟨p, hp, hkey⟩
  rcases key_form_xelements' l (xO i) p hp with ⟨j, hj⟩
  have heq : prev_append i xH = prev_append i (xO j) := by
    calc
      prev_append i xH = prev i := by rfl
      _ = p.1 := hkey.symm
      _ = prev_append (xO i) j := hj
      _ = prev_append i (xO j) := by rfl
  have hbits : xH = xO j := prev_append_injective i heq
  cases hbits

private theorem key_not_in_xI {A : Type} (r : tree' A) (i : positive) :
    prev i ∉ (xelements' r (xI i) []).map Prod.fst := by
  intro h
  rcases List.mem_map.mp h with ⟨p, hp, hkey⟩
  rcases key_form_xelements' r (xI i) p hp with ⟨j, hj⟩
  have heq : prev_append i xH = prev_append i (xI j) := by
    calc
      prev_append i xH = prev i := by rfl
      _ = p.1 := hkey.symm
      _ = prev_append (xI i) j := hj
      _ = prev_append i (xI j) := by rfl
  have hbits : xH = xI j := prev_append_injective i heq
  cases hbits

private theorem keys_nodup_xelements' {A : Type} (m : tree' A) (i : positive) :
    ((xelements' m i []).map Prod.fst).Nodup := by
  induction m generalizing i with
  | Node001 r ih => exact ih (xI i)
  | Node010 x => simp [xelements']
  | Node011 x r ih =>
      simp only [xelements', List.map_cons, List.nodup_cons]
      constructor
      · intro h
        rcases List.mem_map.mp h with ⟨p, hp, hkey⟩
        exact key_not_in_xI r i (by simpa [hkey] using h)
      · exact ih (xI i)
  | Node100 l ih => exact ih (xO i)
  | Node101 l r ihl ihr =>
      change ((xelements' l (xO i) (xelements' r (xI i) [])).map Prod.fst).Nodup
      have hsplit : xelements' l (xO i) (xelements' r (xI i) []) =
          xelements' l (xO i) [] ++ xelements' r (xI i) [] := by
        simpa using (xelements'_append_equation l (xO i) [] (xelements' r (xI i) []))
      rw [hsplit]
      simp only [List.map_append, List.nodup_append]
      exact ⟨ihl (xO i), ihr (xI i), by
        intro a ha b hb hEq
        apply keys_disjoint_xO_xI l r i a ha
        simpa [hEq] using hb⟩
  | Node110 l x ih =>
      change ((xelements' l (xO i) [(prev i, x)]).map Prod.fst).Nodup
      have hsplit : xelements' l (xO i) [(prev i, x)] =
          xelements' l (xO i) [] ++ [(prev i, x)] := by
        simpa using (xelements'_append_equation l (xO i) [] [(prev i, x)])
      rw [hsplit]
      simp only [List.map_append, List.map_singleton]
      rw [List.nodup_append]
      refine ⟨ih (xO i), by simp, ?_⟩
      intro k hk b hb hkb
      have hb' : b = prev i := by simpa using hb
      have hkroot : k = prev i := hkb.trans hb'
      subst b
      apply key_not_in_xO l i
      apply List.mem_map.mpr
      rcases List.mem_map.mp hk with ⟨p, hp, hpk⟩
      refine ⟨p, hp, ?_⟩
      exact hpk.trans hkroot
  | Node111 l x r ihl ihr =>
      change ((xelements' l (xO i)
        ((prev i, x) :: xelements' r (xI i) [])).map Prod.fst).Nodup
      have hsplit : xelements' l (xO i)
          ((prev i, x) :: xelements' r (xI i) []) =
          xelements' l (xO i) [] ++
            ((prev i, x) :: xelements' r (xI i) []) := by
        simpa using (xelements'_append_equation l (xO i) []
          ((prev i, x) :: xelements' r (xI i) []))
      rw [hsplit]
      simp only [List.map_append]
      rw [List.nodup_append]
      have htail : ((prev i, x) :: xelements' r (xI i) []).map Prod.fst |>.Nodup := by
        simp only [List.map_cons, List.nodup_cons]
        exact ⟨key_not_in_xI r i, ihr (xI i)⟩
      refine ⟨ihl (xO i), htail, ?_⟩
      intro k hk b hb hkb
      simp only [List.map_cons, List.mem_cons] at hb
      rcases hb with hroot | hright
      · apply key_not_in_xO l i
        apply List.mem_map.mpr
        rcases List.mem_map.mp hk with ⟨p, hp, hpk⟩
        refine ⟨p, hp, ?_⟩
        exact hpk.trans (hkb.trans hroot)
      · exact (keys_disjoint_xO_xI l r i k hk) (by simpa [hkb] using hright)

theorem elements_complete_proof : elements_completeStatement := by
  intro A m i v h
  cases m with
  | Empty => simp [elements, xelements] at h
  | Nodes m =>
      have hc := in_xelements'_complete m xH (i, v) (by simpa [elements, xelements] using h)
      rcases hc with ⟨j, hj, hget⟩
      have hji : j = i := by
        have hj' : i = prev (prev j) := by simpa [prev] using hj
        rw [prev_involutive] at hj'
        exact hj'.symm
      subst j
      simpa [get] using hget

end PTree

namespace PMap

def elt : Type := positive
def t (A : Type) : Type := A × PTree.t A
def init {A : Type} (x : A) : t A := (x, PTree.empty A)
def get {A : Type} (i : positive) (m : t A) : A :=
  match PTree.get i m.2 with
  | some x => x
  | none => m.1
def set {A : Type} (i : positive) (x : A) (m : t A) : t A := (m.1, PTree.set i x m.2)

def map {A B : Type} (f : A → B) (m : t A) : t B :=
  (f m.1, PTree.map1 f m.2)

def giStatement : Prop := ∀ {A : Type} (i : positive) (x : A), get i (init x) = x
def gssStatement : Prop := ∀ {A : Type} (i : positive) (x : A) (m : t A), get i (set i x m) = x
def gsoStatement : Prop := ∀ {A : Type} {i j : positive} (x : A) (m : t A), i ≠ j → get i (set j x m) = get i m
def gsspecStatement : Prop := ∀ {A : Type} (i j : positive) (x : A) (m : t A),
  get i (set j x m) = match peq i j with | .left _ => x | .right _ => get i m
def gmap : Prop := ∀ {A B : Type} (f : A → B) (i : positive) (m : t A),
  get i (map f m) = f (get i m)
def gmapStatement : Prop := gmap
def set2Statement : Prop := ∀ {A : Type} (i : elt) (x y : A) (m : t A),
  set i y (set i x m) = set i y m

end PMap

namespace ZIndexed

def t : Type := Z

def index : t → positive
  | .Z0 => .xH
  | .Zpos p => .xO p
  | .Zneg p => .xI p

theorem index_inj (x y : t) (h : index x = index y) : x = y := by
  cases x with
  | Z0 =>
      cases y with
      | Z0 => rfl
      | Zpos _ => cases h
      | Zneg _ => cases h
  | Zpos p =>
      cases y with
      | Z0 => cases h
      | Zpos _ => cases h; rfl
      | Zneg _ => cases h
  | Zneg p =>
      cases y with
      | Z0 => cases h
      | Zpos _ => cases h
      | Zneg _ => cases h; rfl

def index_injStatement : Prop := ∀ (x y : t), index x = index y → x = y

def eq (x y : t) : CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) := by
  change Z at x y
  exact if h : x = y then .left h else .right h

end ZIndexed

namespace ZMap

def ZMap : Type := Unit

abbrev elt : Type := ZIndexed.t
abbrev t (A : Type) : Type := PMap.t A

def elt_eq (x y : elt) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  ZIndexed.eq x y

abbrev init {A : Type} (x : A) : t A := PMap.init x
abbrev get {A : Type} (i : elt) (m : t A) : A := PMap.get (ZIndexed.index i) m
abbrev set {A : Type} (i : elt) (x : A) (m : t A) : t A :=
  PMap.set (ZIndexed.index i) x m

def map {A B : Type} (f : A → B) (m : t A) : t B :=
  PMap.map f m

def gi : Prop := ∀ (A : Type) (x : A) (i : elt), get i (init x) = x
def gss : Prop := ∀ (A : Type) (i : elt) (x : A) (m : t A), get i (set i x m) = x
def gso : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  i ≠ j → get i (set j x m) = get i m
def gsspec : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  get i (set j x m) = match elt_eq i j with | .left _ => x | .right _ => get i m
def gmap : Prop := ∀ (A B : Type) (f : A → B) (i : elt) (m : t A),
  get i (map f m) = f (get i m)
def set2 : Prop := ∀ (A : Type) (i : elt) (x y : A) (m : t A),
  set i y (set i x m) = set i y m

end ZMap

namespace NIndexed

def t : Type := N

def index : t → positive
  | .N0 => .xH
  | .Npos p => .xO p

theorem index_inj (x y : t) (h : index x = index y) : x = y := by
  cases x with
  | N0 =>
      cases y with
      | N0 => rfl
      | Npos _ => cases h
  | Npos p =>
      cases y with
      | N0 => cases h
      | Npos _ => cases h; rfl

def index_injStatement : Prop := ∀ (x y : t), index x = index y → x = y

def eq (x y : t) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) := by
  cases x with
  | N0 =>
      cases y with
      | N0 => exact .left rfl
      | Npos p => exact .right (by intro h; cases h)
  | Npos p =>
      cases y with
      | N0 => exact .right (by intro h; cases h)
      | Npos q =>
          match peq p q with
          | .left h => exact .left (by cases h; rfl)
          | .right h => exact .right (by intro hn; cases hn; exact h rfl)

def eqStatement :=
  ∀ (x y : t),
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y)

end NIndexed

namespace NMap

def NMap : Type := Unit

abbrev elt : Type := NIndexed.t
abbrev t (A : Type) : Type := PMap.t A

def elt_eq (x y : elt) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  NIndexed.eq x y

abbrev init {A : Type} (x : A) : t A := PMap.init x
abbrev get {A : Type} (i : elt) (m : t A) : A := PMap.get (NIndexed.index i) m
abbrev set {A : Type} (i : elt) (x : A) (m : t A) : t A :=
  PMap.set (NIndexed.index i) x m

def map {A B : Type} (f : A → B) (m : t A) : t B :=
  PMap.map f m

def gi : Prop := ∀ (A : Type) (x : A) (i : elt), get i (init x) = x
def gss : Prop := ∀ (A : Type) (i : elt) (x : A) (m : t A), get i (set i x m) = x
def gso : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  i ≠ j → get i (set j x m) = get i m
def gsspec : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  get i (set j x m) = match elt_eq i j with | .left _ => x | .right _ => get i m
def gmap : Prop := ∀ (A B : Type) (f : A → B) (i : elt) (m : t A),
  get i (map f m) = f (get i m)
def set2 : Prop := ∀ (A : Type) (i : elt) (x y : A) (m : t A),
  set i y (set i x m) = set i y m

end NMap

namespace ZTree

def ZTree : Type := Unit

abbrev elt : Type := ZIndexed.t
abbrev t (A : Type) : Type := PTree.t A

def elt_eq (x y : elt) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  ZIndexed.eq x y

abbrev empty (A : Type) : t A := PTree.empty A
abbrev get {A : Type} (i : elt) (m : t A) : Option A := PTree.get (ZIndexed.index i) m
abbrev set {A : Type} (i : elt) (x : A) (m : t A) : t A :=
  PTree.set (ZIndexed.index i) x m
abbrev remove {A : Type} (i : elt) (m : t A) : t A := PTree.remove (ZIndexed.index i) m

def gempty : Prop := ∀ (A : Type) (i : elt), get i (empty A) = none
def gss : Prop := ∀ (A : Type) (i : elt) (x : A) (m : t A), get i (set i x m) = some x
def gso : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  i ≠ j → get i (set j x m) = get i m
def gsspec : Prop := ∀ (A : Type) (i j : elt) (x : A) (m : t A),
  get i (set j x m) = match elt_eq i j with | .left _ => some x | .right _ => get i m
def grs : Prop := ∀ (A : Type) (i : elt) (m : t A), get i (remove i m) = none
def gro : Prop := ∀ (A : Type) (i j : elt) (m : t A),
  i ≠ j → get i (remove j m) = get i m
def grspec : Prop := ∀ (A : Type) (i j : elt) (m : t A),
  get i (remove j m) = match elt_eq i j with | .left _ => none | .right _ => get i m

private abbrev beq' {A : Type} (beqA : A → A → Bool) :=
  PTree.beq' beqA

abbrev beq {A : Type} (beqA : A → A → Bool) : t A → t A → Bool :=
  PTree.beq beqA

def beq_sound : Prop := ∀ (A : Type) (eqA : A → A → Bool) (t₁ t₂ : t A),
  beq eqA t₁ t₂ = true → ∀ x : elt,
    match get x t₁, get x t₂ with
    | none, none => True
    | some y₁, some y₂ => eqA y₁ y₂ = true
    | _, _ => False

abbrev combine {A B C : Type} (f : Option A → Option B → Option C)
    (m₁ : t A) (m₂ : t B) : t C := PTree.combine f m₁ m₂

def gcombine : Prop := ∀ (A B C : Type) (f : Option A → Option B → Option C),
  f none none = none → ∀ (m₁ : t A) (m₂ : t B) (i : elt),
    get i (combine f m₁ m₂) = f (get i m₁) (get i m₂)

end ZTree

namespace PTree_Properties

def PTree_Properties : Type := Unit

def fold_ind_aux : Type 1 :=
  ∀ (V A : Type) (f : A → PTree.elt → V → A)
    (P : PTree.t V → A → Type) (init : A) (mFinal : PTree.t V),
    (∀ m, (∀ k, PTree.get k m = none) → P m init) →
    (∀ m a k v, PTree.get k m = some v → PTree.get k mFinal = some v →
      P (PTree.remove k m) a → P m (f a k v)) →
    ∀ l : List (PTree.elt × V),
      (∀ k v, (k, v) ∈ l → PTree.get k mFinal = some v) →
      PTree.list_norepet (l.map Prod.fst) →
      ∀ m, (∀ k v, (k, v) ∈ l ↔ PTree.get k m = some v) →
        P m (List.foldr (fun p a => f a p.1 p.2) init l)

def fold_ind : Type 1 :=
  ∀ (V A : Type) (f : A → PTree.elt → V → A)
    (P : PTree.t V → A → Type) (init : A) (mFinal : PTree.t V),
    (∀ m, (∀ k, PTree.get k m = none) → P m init) →
    (∀ m a k v, PTree.get k m = some v → PTree.get k mFinal = some v →
      P (PTree.remove k m) a → P m (f a k v)) →
    P mFinal (PTree.fold f mFinal init)

def fold_rec : Prop :=
  ∀ (V A : Type) (f : A → PTree.elt → V → A)
    (P : PTree.t V → A → Prop) (init : A) (mFinal : PTree.t V),
    (∀ m m' a, (∀ x, PTree.get x m = PTree.get x m') → P m a → P m' a) →
    P (PTree.empty V) init →
    (∀ m a k v, PTree.get k m = none → PTree.get k mFinal = some v →
      P m a → P (PTree.set k v m) (f a k v)) →
    P mFinal (PTree.fold f mFinal init)

def cardinal {V : Type} (m : PTree.t V) : Nat := (PTree.elements m).length

def cardinal_remove : Prop := ∀ (V : Type) (x : PTree.elt) (m : PTree.t V) (y : V),
  PTree.get x m = some y → cardinal (PTree.remove x m) < cardinal m
def cardinal_set : Prop := ∀ (V : Type) (x : PTree.elt) (m : PTree.t V) (y : V),
  PTree.get x m = none → cardinal m < cardinal (PTree.set x y m)

private def treeCard' {A : Type} : PTree.tree' A → Nat
  | .Node001 r => treeCard' r
  | .Node010 _ => 1
  | .Node011 _ r => 1 + treeCard' r
  | .Node100 l => treeCard' l
  | .Node101 l r => treeCard' l + treeCard' r
  | .Node110 l _ => treeCard' l + 1
  | .Node111 l _ r => treeCard' l + 1 + treeCard' r

private def treeCard {A : Type} : PTree.tree A → Nat
  | .Empty => 0
  | .Nodes m => treeCard' m

private def optionCard {A : Type} : Option A → Nat
  | none => 0
  | some _ => 1

private theorem treeCard_node {A : Type} (l : PTree.tree A) (o : Option A)
    (r : PTree.tree A) :
    treeCard (PTree.Node l o r) = treeCard l + optionCard o + treeCard r := by
  cases l <;> cases o <;> cases r <;>
    simp [PTree.Node, treeCard, treeCard', optionCard]

private theorem xelements_length {A : Type} (m : PTree.tree' A) (i : positive)
    (suffix : List (positive × A)) :
    (PTree.xelements' m i suffix).length = treeCard' m + suffix.length := by
  induction m generalizing i suffix <;>
    simp_all [PTree.xelements', treeCard', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem cardinal_eq_treeCard {A : Type} (m : PTree.tree A) :
    cardinal m = treeCard m := by
  cases m with
  | Empty => rfl
  | Nodes m =>
      simpa [cardinal, PTree.elements, PTree.xelements, treeCard]
        using xelements_length m .xH []

private theorem treeCard_remove_lt {A : Type} (p : positive) (m : PTree.tree' A)
    (v : A) (h : PTree.get' p m = some v) :
    treeCard (PTree.remove' p m) < treeCard' m := by
  induction p generalizing m with
  | xH =>
      cases m <;> simp_all [PTree.get', PTree.remove', treeCard, treeCard']
  | xO p ih =>
      cases m <;> simp_all [PTree.get', PTree.remove', treeCard, treeCard']
      all_goals
        have decrease := ih _ h
        cases hrem : PTree.remove' p _ <;>
          simp [PTree.remove', hrem, treeCard, treeCard'] at decrease ⊢ <;> omega
  | xI p ih =>
      cases m <;> simp_all [PTree.get', PTree.remove', treeCard, treeCard']
      all_goals
        have decrease := ih _ h
        cases hrem : PTree.remove' p _ <;>
          simp [PTree.remove', hrem, treeCard, treeCard'] at decrease ⊢ <;> omega

theorem cardinal_remove_proof : cardinal_remove := by
  intro V x m y h
  rw [show cardinal (PTree.remove x m) = treeCard (PTree.remove x m) by
        exact cardinal_eq_treeCard _]
  rw [show cardinal m = treeCard m by exact cardinal_eq_treeCard _]
  cases m with
  | Empty => simp [PTree.get] at h
  | Nodes m =>
      exact treeCard_remove_lt x m y (by simpa [PTree.get] using h)

def for_all {A : Type} (m : PTree.t A) (f : PTree.elt → A → Bool) : Bool :=
  PTree.fold (fun b x a => b && f x a) m true

def for_all_correct : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  for_all m f = true ↔ ∀ x a, PTree.get x m = some a → f x a = true

private theorem foldl_and_true {A : Type} (f : positive → A → Bool) :
    ∀ (l : List (positive × A)) (acc : Bool),
      List.foldl (fun b p => b && f p.1 p.2) acc l = true ↔
        acc = true ∧ ∀ p ∈ l, f p.1 p.2 = true := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons p l ih =>
      intro acc
      simp only [List.foldl, ih, Bool.and_eq_true, List.mem_cons]
      constructor
      · rintro ⟨⟨hacc, hp⟩, htail⟩
        exact ⟨hacc, by
          intro q hq
          rcases hq with rfl | hq
          · exact hp
          · exact htail q hq⟩
      · rintro ⟨hacc, hall⟩
        exact ⟨⟨hacc, hall p (by simp)⟩, by
          intro q hq
          exact hall q (by simp [hq])⟩

theorem for_all_correct_proof : for_all_correct := by
  intro A m f
  change positive → A → Bool at f
  rw [show for_all m f =
      List.foldl (fun b p => b && f p.1 p.2) true (PTree.elements m) by
        simpa [for_all, PTree.fold_specStatement] using
          PTree.fold_spec_proof (B := Bool) (fun b x a => b && f x a) true m]
  rw [foldl_and_true]
  simp only [Bool.true_eq, true_and]
  constructor
  · intro hall x a hget
    exact hall (x, a) (PTree.elements_correct_proof m x (v := a) hget)
  · intro h p hp
    rcases p with ⟨x, a⟩
    exact h x a (PTree.elements_complete_proof m x a hp)

def exists_ {A : Type} (m : PTree.t A) (f : PTree.elt → A → Bool) : Bool :=
  PTree.fold (fun b x a => b || f x a) m false

def exists_correct : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  exists_ m f = true ↔ ∃ x a, PTree.get x m = some a ∧ f x a = true
def exists_for_all : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  exists_ m f = Bool.not (for_all m (fun x a => Bool.not (f x a)))
def for_all_exists : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  for_all m f = Bool.not (exists_ m (fun x a => Bool.not (f x a)))
def for_all_false : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  for_all m f = false ↔ ∃ x a, PTree.get x m = some a ∧ f x a = false
def exists_false : Prop := ∀ (A : Type) (m : PTree.t A) (f : PTree.elt → A → Bool),
  exists_ m f = false ↔ ∀ x a, PTree.get x m = some a → f x a = false

def beq_false : Prop := ∀ (A : Type) (beqA : A → A → Bool) (m₁ m₂ : PTree.t A),
  PTree.beq beqA m₁ m₂ = false ↔ ∃ x : PTree.elt,
    match PTree.get x m₁, PTree.get x m₂ with
    | none, none => False
    | some a₁, some a₂ => beqA a₁ a₂ = false
    | _, _ => True

def Equal {A : Type} (eqA : A → A → Prop) (_eqAeq : Equivalence eqA)
    (m₁ m₂ : PTree.t A) : Prop :=
  ∀ x, match PTree.get x m₁, PTree.get x m₂ with
    | none, none => True
    | some a₁, some a₂ => eqA a₁ a₂
    | _, _ => False

private theorem proj_sumbool_true {P Q : Prop}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q)
    (h : proj_sumbool d = true) : P := by
  cases d with
  | left hp => exact hp
  | right hq => simp [proj_sumbool] at h

private theorem proj_sumbool_false {P Q : Prop}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q)
    (h : proj_sumbool d = false) : Q := by
  cases d with
  | left hp => simp [proj_sumbool] at h
  | right hq => exact hq

private theorem proj_sumbool_of_true {P : Prop}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P (¬ P))
    (h : P) : proj_sumbool d = true := by
  cases d with
  | left hp => rfl
  | right hq => exact (hq h).elim

private theorem bool_and_true {a b : Bool} (h : a && b = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private def beq_opt {A : Type} (beqA : A → A → Bool) :
    Option A → Option A → Bool
  | none, none => true
  | some a₁, some a₂ => beqA a₁ a₂
  | _, _ => false

private theorem beq_node {A : Type} (beqA : A → A → Bool)
    (l₁ : PTree.t A) (o₁ : Option A) (r₁ : PTree.t A)
    (l₂ : PTree.t A) (o₂ : Option A) (r₂ : PTree.t A)
    (h₁ : PTree.not_trivially_empty l₁ o₁ r₁)
    (h₂ : PTree.not_trivially_empty l₂ o₂ r₂) :
    PTree.beq beqA (PTree.Node l₁ o₁ r₁) (PTree.Node l₂ o₂ r₂) =
      ((PTree.beq beqA l₁ l₂ && beq_opt beqA o₁ o₂) &&
        PTree.beq beqA r₁ r₂) := by
  cases l₁ <;> cases o₁ <;> cases r₁ <;>
    cases l₂ <;> cases o₂ <;> cases r₂ <;>
      simp_all [PTree.Node, PTree.not_trivially_empty, PTree.beq,
        PTree.beq', beq_opt, Bool.and_assoc, Bool.and_left_comm,
        Bool.and_comm]

private theorem tree'_witness {A : Type} :
    ∀ m : PTree.tree' A, ∃ p v, PTree.get' p m = some v := by
  intro m
  induction m with
  | Node001 r ih =>
      rcases ih with ⟨p, v, hv⟩
      exact ⟨.xI p, v, by simpa [PTree.get'] using hv⟩
  | Node010 x => exact ⟨.xH, x, by simp [PTree.get']⟩
  | Node011 x r ih => exact ⟨.xH, x, by simp [PTree.get']⟩
  | Node100 l ih =>
      rcases ih with ⟨p, v, hv⟩
      exact ⟨.xO p, v, by simpa [PTree.get'] using hv⟩
  | Node101 l r ihl ihr =>
      rcases ihl with ⟨p, v, hv⟩
      exact ⟨.xO p, v, by simpa [PTree.get'] using hv⟩
  | Node110 l x ih =>
      rcases ih with ⟨p, v, hv⟩
      exact ⟨.xO p, v, by simpa [PTree.get'] using hv⟩
  | Node111 l x r ihl ihr => exact ⟨.xH, x, by simp [PTree.get']⟩

private theorem node_not_empty {A : Type} (l : PTree.t A) (o : Option A)
    (r : PTree.t A) (h : PTree.not_trivially_empty l o r) :
    PTree.Node l o r ≠ .Empty := by
  intro hn
  cases l <;> cases o <;> cases r <;>
    simp_all [PTree.Node, PTree.not_trivially_empty]

private theorem node_witness {A : Type} (l : PTree.t A) (o : Option A)
    (r : PTree.t A) (h : PTree.not_trivially_empty l o r) :
    ∃ p v, PTree.get p (PTree.Node l o r) = some v := by
  have hne := node_not_empty l o r h
  cases hnode : PTree.Node l o r with
  | Empty => exact (hne hnode).elim
  | Nodes m =>
      rcases tree'_witness m with ⟨p, v, hv⟩
      exact ⟨p, v, by simpa [hnode, PTree.get] using hv⟩

private theorem get_node_at {A : Type} (i : positive) (l : PTree.t A)
    (o : Option A) (r : PTree.t A) :
    PTree.get i (PTree.Node l o r) =
      match i with
      | .xH => o
      | .xO p => PTree.get p l
      | .xI p => PTree.get p r := by
  cases i <;> cases l <;> cases o <;> cases r <;> rfl

private theorem extensional_beq_true {A : Type} (beqA : A → A → Bool) :
    ∀ (m₁ m₂ : PTree.t A),
      (∀ x, beq_opt beqA (PTree.get x m₁) (PTree.get x m₂) = true) →
        PTree.beq beqA m₁ m₂ = true := by
  intro m₁
  have hP : PLift (∀ m₂ : PTree.t A,
      (∀ x, beq_opt beqA (PTree.get x m₁) (PTree.get x m₂) = true) →
        PTree.beq beqA m₁ m₂ = true) := by
    refine PTree.tree_ind
        (P := fun m₁ => PLift (∀ m₂ : PTree.t A,
          (∀ x, beq_opt beqA (PTree.get x m₁) (PTree.get x m₂) = true) →
            PTree.beq beqA m₁ m₂ = true)) ?_ ?_ m₁
    · refine ⟨?_⟩
      intro m₂ H
      cases m₂ with
      | Empty => rfl
      | Nodes m₂ =>
          rcases tree'_witness m₂ with ⟨p, v, hv⟩
          have hx := H p
          have hfalse : False := by
            simp only [PTree.get] at hx
            rw [hv] at hx
            simpa [PTree.get, beq_opt] using hx
          exact hfalse.elim
    · intro l il o r ir hne
      refine ⟨?_⟩
      intro m₂
      have hP₂ : PLift (
          (∀ x, beq_opt beqA (PTree.get x (PTree.Node l o r))
              (PTree.get x m₂) = true) →
            PTree.beq beqA (PTree.Node l o r) m₂ = true) := by
        refine PTree.tree_ind
            (P := fun m₂ => PLift (
              (∀ x, beq_opt beqA (PTree.get x (PTree.Node l o r))
                  (PTree.get x m₂) = true) →
                PTree.beq beqA (PTree.Node l o r) m₂ = true)) ?_ ?_ m₂
        · refine ⟨?_⟩
          intro H
          rcases node_witness l o r hne with ⟨p, v, hv⟩
          have hx := H p
          have hfalse : False := by
            rw [hv] at hx
            simpa [PTree.get, beq_opt] using hx
          exact hfalse.elim
        · intro l₂ il₂ o₂ r₂ ir₂ hne₂
          refine ⟨?_⟩
          intro H
          have hleft : ∀ p,
              beq_opt beqA (PTree.get p l) (PTree.get p l₂) = true := by
            intro p
            have hx := H (.xO p)
            rw [get_node_at (.xO p) l o r,
              get_node_at (.xO p) l₂ o₂ r₂] at hx
            simpa [beq_opt] using hx
          have hroot : beq_opt beqA o o₂ = true := by
            have hx := H .xH
            rw [get_node_at .xH l o r,
              get_node_at .xH l₂ o₂ r₂] at hx
            simpa [beq_opt] using hx
          have hright : ∀ p,
              beq_opt beqA (PTree.get p r) (PTree.get p r₂) = true := by
            intro p
            have hx := H (.xI p)
            rw [get_node_at (.xI p) l o r,
              get_node_at (.xI p) l₂ o₂ r₂] at hx
            simpa [beq_opt] using hx
          have hleft_beq := PLift.down il l₂ hleft
          have hright_beq := PLift.down ir r₂ hright
          rw [beq_node beqA l o r l₂ o₂ r₂ hne hne₂]
          simp [hleft_beq, hroot, hright_beq]
      exact PLift.down hP₂
  exact PLift.down hP

private theorem equal_beq_true {A : Type}
    (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
    (eqAdec : ∀ a₁ a₂,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (eqA a₁ a₂) (¬ eqA a₁ a₂)) :
    ∀ (m₁ m₂ : PTree.t A),
      Equal eqA eqAeq m₁ m₂ →
        PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) m₁ m₂ = true := by
  intro m₁ m₂ hEq
  apply extensional_beq_true
  intro x
  cases h₁ : PTree.get x m₁ with
  | none =>
      cases h₂ : PTree.get x m₂ with
      | none => simp [beq_opt, h₁, h₂]
      | some a₂ =>
          have hfalse : False := by
            simpa [Equal, h₁, h₂] using hEq x
          exact hfalse.elim
  | some a₁ =>
      cases h₂ : PTree.get x m₂ with
      | none =>
          have hfalse : False := by
            simpa [Equal, h₁, h₂] using hEq x
          exact hfalse.elim
      | some a₂ =>
          have hea : eqA a₁ a₂ := by
            simpa [Equal, h₁, h₂] using hEq x
          have hb := proj_sumbool_of_true (eqAdec a₁ a₂) hea
          simp [beq_opt, h₁, h₂, hb]


private theorem beq_true_equal {A : Type}
    (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
    (eqAdec : ∀ a₁ a₂,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (eqA a₁ a₂) (¬ eqA a₁ a₂)) :
    ∀ (m₁ m₂ : PTree.t A),
      PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) m₁ m₂ = true →
        Equal eqA eqAeq m₁ m₂ := by
  intro m₁ m₂ h
  cases m₁ with
  | Empty =>
      cases m₂ with
      | Empty => intro x; simp [Equal, PTree.get]
      | Nodes m₂ => simp [PTree.beq] at h
  | Nodes m₁ =>
      cases m₂ with
      | Empty => simp [PTree.beq] at h
      | Nodes m₂ =>
          induction m₁ generalizing m₂ with
          | Node001 r ih =>
              cases m₂ with
              | Node001 r₂ =>
                  simp only [PTree.beq, PTree.beq', Bool.true_eq] at h
                  intro x
                  cases x with
                  | xH => simp [Equal, PTree.get, PTree.get']
                  | xO q => simp [Equal, PTree.get, PTree.get']
                  | xI q => simpa [Equal, PTree.get, PTree.get'] using ih r₂ h q
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node010 x₁ =>
              cases m₂ with
              | Node010 x₂ =>
                  have hx : eqA x₁ x₂ := proj_sumbool_true (eqAdec x₁ x₂) (by simpa [PTree.beq, PTree.beq'] using h)
                  intro x
                  cases x with
                  | xH => simpa [Equal, PTree.get, PTree.get'] using hx
                  | xO q => simp [Equal, PTree.get, PTree.get']
                  | xI q => simp [Equal, PTree.get, PTree.get']
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node011 x₁ r ih =>
              cases m₂ with
              | Node011 x₂ r₂ =>
                  have hparts := bool_and_true (by simpa [PTree.beq, PTree.beq'] using h)
                  have hx : eqA x₁ x₂ := proj_sumbool_true (eqAdec x₁ x₂) hparts.1
                  have hr : PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) (.Nodes r) (.Nodes r₂) = true := by
                    simpa [PTree.beq, PTree.beq'] using hparts.2
                  intro x
                  cases x with
                  | xH => simpa [Equal, PTree.get, PTree.get'] using hx
                  | xO q => simp [Equal, PTree.get, PTree.get']
                  | xI q => simpa [Equal, PTree.get, PTree.get'] using ih r₂ hr q
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node100 l ih =>
              cases m₂ with
              | Node100 l₂ =>
                  intro x
                  have hl : PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) (.Nodes l) (.Nodes l₂) = true := by simpa [PTree.beq, PTree.beq'] using h
                  cases x with
                  | xH => simp [Equal, PTree.get, PTree.get']
                  | xO q => simpa [Equal, PTree.get, PTree.get'] using ih l₂ hl q
                  | xI q => simp [Equal, PTree.get, PTree.get']
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node101 l r ihl ihr =>
              cases m₂ with
              | Node101 l₂ r₂ =>
                  have hparts := bool_and_true (by simpa [PTree.beq, PTree.beq'] using h)
                  have hl : PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) (.Nodes l) (.Nodes l₂) = true := by simpa [PTree.beq, PTree.beq'] using hparts.1
                  have hr : PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) (.Nodes r) (.Nodes r₂) = true := by simpa [PTree.beq, PTree.beq'] using hparts.2
                  intro x
                  cases x with
                  | xH => simp [Equal, PTree.get, PTree.get']
                  | xO q => simpa [Equal, PTree.get, PTree.get'] using ihl l₂ hl q
                  | xI q => simpa [Equal, PTree.get, PTree.get'] using ihr r₂ hr q
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node110 l x₁ ih =>
              cases m₂ with
              | Node110 l₂ x₂ =>
                  have hparts := bool_and_true (by simpa [PTree.beq, PTree.beq'] using h)
                  have hx : eqA x₁ x₂ := proj_sumbool_true (eqAdec x₁ x₂) hparts.1
                  have hl : PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) (.Nodes l) (.Nodes l₂) = true := by simpa [PTree.beq, PTree.beq'] using hparts.2
                  intro x
                  cases x with
                  | xH => simpa [Equal, PTree.get, PTree.get'] using hx
                  | xO q => simpa [Equal, PTree.get, PTree.get'] using ih l₂ hl q
                  | xI q => simp [Equal, PTree.get, PTree.get']
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node111 l x₁ r ihl ihr =>
              cases m₂ with
              | Node111 l₂ x₂ r₂ =>
                  have hbool :
                      (proj_sumbool (eqAdec x₁ x₂) &&
                        PTree.beq' (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) l l₂) &&
                        PTree.beq' (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) r r₂ = true := by
                    simpa [PTree.beq, PTree.beq'] using h
                  have hparts₁ := bool_and_true hbool
                  have hleft :
                      (proj_sumbool (eqAdec x₁ x₂) &&
                        PTree.beq' (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) l l₂) = true :=
                    hparts₁.1
                  have hparts₂ :
                      proj_sumbool (eqAdec x₁ x₂) = true ∧
                        PTree.beq' (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) l l₂ = true := by
                    cases h₁ : proj_sumbool (eqAdec x₁ x₂) with
                    | false => simp [h₁] at hleft
                    | true =>
                        cases h₂ : PTree.beq' (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) l l₂ with
                        | false => simp [h₁, h₂] at hleft
                        | true => exact ⟨rfl, rfl⟩
                  have hx : eqA x₁ x₂ := proj_sumbool_true (eqAdec x₁ x₂) hparts₂.1
                  have hl : PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) (.Nodes l) (.Nodes l₂) = true := by simpa [PTree.beq, PTree.beq'] using hparts₂.2
                  have hr : PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) (.Nodes r) (.Nodes r₂) = true := by simpa [PTree.beq, PTree.beq'] using hparts₁.2
                  intro x
                  cases x with
                  | xH => simpa [Equal, PTree.get, PTree.get'] using hx
                  | xO q => simpa [Equal, PTree.get, PTree.get'] using ihl l₂ hl q
                  | xI q => simpa [Equal, PTree.get, PTree.get'] using ihr r₂ hr q
              | _ => simp [PTree.beq, PTree.beq'] at h

def Equal_refl : Prop := ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
  (m : PTree.t A), Equal eqA eqAeq m m
def Equal_sym : Prop := ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
  (m₁ m₂ : PTree.t A), Equal eqA eqAeq m₁ m₂ → Equal eqA eqAeq m₂ m₁
def Equal_trans : Prop := ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
  (m₁ m₂ m₃ : PTree.t A), Equal eqA eqAeq m₁ m₂ → Equal eqA eqAeq m₂ m₃ →
    Equal eqA eqAeq m₁ m₃
def Equal_Equivalence : Prop := ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA),
  Equivalence (Equal eqA eqAeq)

def Equal_dec_obligation_1 : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
    (eqAdec : ∀ a₁ a₂,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (eqA a₁ a₂) (¬ eqA a₁ a₂))
    (m₁ m₂ : PTree.t A),
    let filtered_var :=
      PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) m₁ m₂
    ∀ Heq_anonymous : true = filtered_var,
      Equal eqA eqAeq m₁ m₂
def Equal_dec_obligation_2 : Prop :=
  ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA)
    (eqAdec : ∀ a₁ a₂,
      CompCert4Lean.Foundation.Logic.Support.Sumbool (eqA a₁ a₂) (¬ eqA a₁ a₂))
    (m₁ m₂ : PTree.t A),
    let filtered_var :=
      PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) m₁ m₂
    false = filtered_var →
      ¬ Equal eqA eqAeq m₁ m₂

def Equal_dec :
    ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA),
      (∀ a₁ a₂,
        CompCert4Lean.Foundation.Logic.Support.Sumbool
          (eqA a₁ a₂) (¬ eqA a₁ a₂)) →
      ∀ m₁ m₂ : PTree.t A,
        CompCert4Lean.Foundation.Logic.Support.Sumbool
          (Equal eqA eqAeq m₁ m₂) (¬ Equal eqA eqAeq m₁ m₂) := by
  intro A eqA eqAeq eqAdec m₁ m₂
  cases h : PTree.beq (fun a₁ a₂ => proj_sumbool (eqAdec a₁ a₂)) m₁ m₂ with
  | true => exact .left (beq_true_equal eqA eqAeq eqAdec m₁ m₂ h)
  | false =>
      exact .right (by
          intro hEq
          have hb := equal_beq_true eqA eqAeq eqAdec m₁ m₂ hEq
          simp [h] at hb)

def Equal_EqDec :
    ∀ (A : Type) (eqA : A → A → Prop) (eqAeq : Equivalence eqA),
      (∀ a₁ a₂,
        CompCert4Lean.Foundation.Logic.Support.Sumbool
          (eqA a₁ a₂) (¬ eqA a₁ a₂)) →
      ∀ m₁ m₂ : PTree.t A,
        CompCert4Lean.Foundation.Logic.Support.Sumbool
          (Equal eqA eqAeq m₁ m₂) (¬ Equal eqA eqAeq m₁ m₂) :=
  Equal_dec

def of_list {A : Type} (l : List (PTree.elt × A)) : PTree.t A :=
  List.foldl (fun m kv => PTree.set kv.1 kv.2 m) (PTree.empty A) l

private def set_list {A : Type} (m : PTree.tree A) (l : List (positive × A)) : PTree.tree A :=
  List.foldl (fun m kv => PTree.set kv.1 kv.2 m) m l

private theorem get_set_list_preserve {A : Type} (m : PTree.tree A)
    (l : List (positive × A)) (k : positive)
    (hkeys : k ∉ l.map Prod.fst) :
    PTree.get k (set_list m l) = PTree.get k m := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
      rcases p with ⟨j, v⟩
      have hne : k ≠ j := by
        intro hkj
        apply hkeys
        simp [hkj]
      have htail : k ∉ l.map Prod.fst := by
        intro hmem
        apply hkeys
        simp [hmem]
      change PTree.get k (set_list (PTree.set j v m) l) = PTree.get k m
      rw [ih (PTree.set j v m) htail]
      simpa [PTree.getSet_equation, hne]

private theorem get_set_list_none {A : Type} (m : PTree.tree A)
    (l : List (positive × A)) (k : positive)
    (h0 : PTree.get k m = none) (hkeys : k ∉ l.map Prod.fst) :
    PTree.get k (set_list m l) = none := by
  simpa [set_list] using get_set_list_preserve m l k hkeys |>.trans h0

private theorem get_set_list_some {A : Type} (m : PTree.tree A)
    (l : List (positive × A)) (k : positive) (v : A)
    (hnodup : (l.map Prod.fst).Nodup) (hmem : (k, v) ∈ l) :
    PTree.get k (set_list m l) = some v := by
  induction l generalizing m k v with
  | nil => cases hmem
  | cons p l ih =>
      rcases p with ⟨j, w⟩
      have htailnodup : (l.map Prod.fst).Nodup := (List.nodup_cons.mp hnodup).2
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        have hpres := get_set_list_preserve (PTree.set k v m) l k
          (by simpa using (List.nodup_cons.mp hnodup).1)
        change PTree.get k (set_list (PTree.set k v m) l) = some v
        rw [hpres]
        simp [PTree.getSet_equation]
      · have hne : k ≠ j := by
          intro hkj
          apply (List.nodup_cons.mp hnodup).1
          apply List.mem_map.mpr
          exact ⟨(k, v), htail, hkj⟩
        have hstep := ih (PTree.set j w m) k v htailnodup htail
        simpa [set_list, List.foldl] using hstep

private theorem get_set_list_dom {A : Type} (m : PTree.tree A)
    (l : List (positive × A)) (k : positive) (y : A)
    (h0 : PTree.get k m = none)
    (hget : PTree.get k (set_list m l) = some y) :
    ∃ v, (k, v) ∈ l := by
  induction l generalizing m k y with
  | nil =>
      change PTree.get k m = some y at hget
      rw [h0] at hget
      cases hget
  | cons p l ih =>
      rcases p with ⟨j, v⟩
      by_cases hkj : k = j
      · exact ⟨v, by simp [hkj]⟩
      · have hstep : PTree.get k (PTree.set j v m) = none := by
          simpa [PTree.getSet_equation, hkj] using h0
        have htailget := ih (PTree.set j v m) k y hstep
          (by simpa [set_list, List.foldl] using hget)
        rcases htailget with ⟨w, hw⟩
        exact ⟨w, List.mem_cons_of_mem _ hw⟩



def in_of_list : Prop := ∀ (A : Type) (l : List (PTree.elt × A)) (k : PTree.elt) (v : A),
  PTree.get k (of_list l) = some v → (k, v) ∈ l
def of_list_dom : Prop := ∀ (A : Type) (l : List (PTree.elt × A)) (k : PTree.elt),
  k ∈ l.map Prod.fst → ∃ v, PTree.get k (of_list l) = some v
def of_list_unchanged : Prop := ∀ (A : Type) (k : PTree.elt) (l : List (PTree.elt × A))
  (m : PTree.t A), k ∉ l.map Prod.fst →
    PTree.get k (List.foldl (fun m₀ kv => PTree.set kv.1 kv.2 m₀) m l) = PTree.get k m
def of_list_unique : Prop := ∀ (A : Type) (k : PTree.elt) (v : A)
  (l₁ l₂ : List (PTree.elt × A)), k ∉ l₂.map Prod.fst →
    PTree.get k (of_list (l₁ ++ (k, v) :: l₂)) = some v
def of_list_norepet : Prop := ∀ (A : Type) (l : List (PTree.elt × A)) (k : PTree.elt) (v : A),
  PTree.list_norepet (l.map Prod.fst) → (k, v) ∈ l → PTree.get k (of_list l) = some v
def of_list_elements : Prop := ∀ (A : Type) (m : PTree.t A) (k : PTree.elt),
  PTree.get k (of_list (PTree.elements m)) = PTree.get k m

theorem of_list_elements_proof : of_list_elements := by
  intro A m k
  have hcorrect : ∀ (i : positive) (v : A),
      PTree.get i m = some v → (i, v) ∈ PTree.elements m := by
    simpa [PTree.elements_correctStatement] using (PTree.elements_correct_proof (m := m))
  have hcomplete : ∀ (i : positive) (v : A),
      (i, v) ∈ PTree.elements m → PTree.get i m = some v := by
    simpa [PTree.elements_completeStatement] using (PTree.elements_complete_proof (m := m))
  have hnodup : (PTree.elements m).map Prod.fst |>.Nodup := by
    cases m with
    | Empty => simp [PTree.elements, PTree.xelements]
    | Nodes m =>
        simpa [PTree.elements, PTree.xelements] using
          PTree.keys_nodup_xelements' m .xH
  cases hkm : PTree.get k m with
  | none =>
      have hnone : k ∉ (PTree.elements m).map Prod.fst := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨p, hp, hpk⟩
        have hg := hcomplete p.1 p.2 hp
        have hg' : PTree.get k m = some p.2 := by simpa [hpk] using hg
        rw [hkm] at hg'
        cases hg'
      have hres := get_set_list_none (PTree.empty A) (PTree.elements m) k
        (by rfl) hnone
      change PTree.get k (List.foldl (fun m kv => PTree.set kv.1 kv.2 m)
        (PTree.empty A) (PTree.elements m)) = none
      exact hres
  | some y =>
      have hmem := hcorrect k y (by simpa [hkm] using hkm)
      have hres := get_set_list_some (PTree.empty A) (PTree.elements m) k y hnodup hmem
      change PTree.get k (List.foldl (fun m kv => PTree.set kv.1 kv.2 m)
        (PTree.empty A) (PTree.elements m)) = some y
      exact hres

theorem fold_rec_proof : fold_rec := by
  intro V A f P init mFinal hext hbase hstep
  have hcomplete : ∀ (i : positive) (v : V),
      (i, v) ∈ PTree.elements mFinal → PTree.get i mFinal = some v := by
    simpa [PTree.elements_completeStatement] using (PTree.elements_complete_proof (m := mFinal))
  have hnodup : (PTree.elements mFinal).map Prod.fst |>.Nodup := by
    cases mFinal with
    | Empty => simp [PTree.elements, PTree.xelements]
    | Nodes m =>
        simpa [PTree.elements, PTree.xelements] using
          PTree.keys_nodup_xelements' m .xH
  have hprocess : ∀ (m : PTree.tree V) (a : A) (l : List (positive × V)),
      P m a →
      (∀ p, p ∈ l → p ∈ PTree.elements mFinal) →
      (∀ p, p ∈ l → PTree.get p.1 m = none) →
      (l.map Prod.fst).Nodup →
      P (set_list m l)
        (List.foldl (fun a p => f a p.1 p.2) a l) := by
    intro m a l hP hsub hnone hlist
    induction l generalizing m a with
    | nil => simpa only [set_list, List.foldl] using hP
    | cons p l ih =>
        rcases p with ⟨k, v⟩
        simp only [List.map_cons, List.nodup_cons] at hlist
        have hsubhead : (k, v) ∈ PTree.elements mFinal := by simp [hsub]
        have hsubtail : ∀ q, q ∈ l → q ∈ PTree.elements mFinal := by
          intro q hq
          apply hsub q
          simp [hq]
        have hnonehead : PTree.get k m = none := hnone (k, v) (by simp)
        have hfinal := hcomplete k v hsubhead
        have hnext := hstep m a k v hnonehead hfinal hP
        have hnoneTail : ∀ q, q ∈ l → PTree.get q.1 (PTree.set k v m) = none := by
          intro q hq
          have hqkey : q.1 ≠ k := by
            intro heq
            apply hlist.1
            apply List.mem_map.mpr
            exact ⟨q, hq, heq⟩
          have hqnone := hnone q (by simp [hq])
          simpa [PTree.getSet_equation, hqkey] using hqnone
        have htail := ih (PTree.set k v m) (f a k v) hnext hsubtail
          hnoneTail hlist.2
        simpa [set_list, List.foldl] using htail
  have hfinal := hprocess (PTree.empty V) init (PTree.elements mFinal) hbase
    (by intro p hp; exact hp)
    (by intro p hp; rfl) hnodup
  have hmap : ∀ x, PTree.get x (set_list (PTree.empty V) (PTree.elements mFinal)) =
      PTree.get x mFinal := by
    change ∀ x, PTree.get x (List.foldl (fun m kv => PTree.set kv.1 kv.2 m)
      (PTree.empty V) (PTree.elements mFinal)) = PTree.get x mFinal
    intro x
    exact of_list_elements_proof V mFinal x
  have hp := hext (set_list (PTree.empty V) (PTree.elements mFinal)) mFinal
    (List.foldl (fun a p => f a p.1 p.2) init (PTree.elements mFinal)) hmap hfinal
  have hfold : PTree.fold f mFinal init =
      List.foldl (fun a p => f a p.1 p.2) init (PTree.elements mFinal) := by
    simpa [PTree.fold_specStatement] using
      (PTree.fold_spec_proof (A := V) (B := A) f init mFinal)
  rw [hfold]
  exact hp

def of_list_related : Prop := ∀ (A B : Type) (R : A → B → Prop) (k : PTree.elt)
  (l₁ : List (PTree.elt × A)) (l₂ : List (PTree.elt × B)),
  PTree.list_forall2 (fun ka kb => ka.1 = kb.1 ∧ R ka.2 kb.2) l₁ l₂ →
    PTree.option_rel R (PTree.get k (of_list l₁)) (PTree.get k (of_list l₂))

end PTree_Properties

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

namespace PTree

theorem gempty : gemptyStatement := by
  intro A i
  rfl

theorem gss0 : gss0Statement := by
  intro A p x
  induction p with
  | xH => rfl
  | xO p ih => simpa [get', set0] using ih
  | xI p ih => simpa [get', set0] using ih

theorem gso0 : gso0Statement := by
  intro A p q x hpq
  induction p generalizing q with
  | xH =>
      cases q <;> simp [get', set0] at hpq ⊢
  | xO p ih =>
      cases q with
      | xH => rfl
      | xO q =>
          simp only [set0, get']
          apply ih
          intro hpq'
          apply hpq
          simpa [hpq']
      | xI q => rfl
  | xI p ih =>
      cases q with
      | xH => rfl
      | xO q => rfl
      | xI q =>
          simp only [set0, get']
          apply ih
          intro hpq'
          apply hpq
          simpa [hpq']

theorem gss : gssStatement := by
  intro A i x m
  simpa using getSet_equation i i x m

end PTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

namespace PTree

theorem gso : gsoStatement := by
  intro A i j x m hij
  simpa [hij] using (getSet_equation i j x m)

theorem unroll_tree_rec : unroll_tree_recStatement := by
  intro A B emptyCase node l o r h
  cases l <;> cases o <;> cases r <;>
    simp_all [not_trivially_empty, Node, tree_rec, tree_rec']

theorem tree'_not_empty : tree'_not_emptyStatement := by
  intro A m
  induction m with
  | Node001 r ih =>
      rcases ih with ⟨i, hi⟩
      exact ⟨.xI i, hi⟩
  | Node010 x =>
      exact ⟨.xH, by simp [get']⟩
  | Node011 x r ih =>
      exact ⟨.xH, by simp [get']⟩
  | Node100 l ih =>
      rcases ih with ⟨i, hi⟩
      exact ⟨.xO i, hi⟩
  | Node101 l r ihl ihr =>
      rcases ihl with ⟨i, hi⟩
      exact ⟨.xO i, hi⟩
  | Node110 l x ih =>
      exact ⟨.xH, by simp [get']⟩
  | Node111 l x r ihl ihr =>
      exact ⟨.xH, by simp [get']⟩

theorem extensionality_empty : extensionality_emptyStatement := by
  intro A m h
  cases m with
  | Empty => rfl
  | Nodes m =>
      rcases tree'_not_empty m with ⟨i, hi⟩
      exfalso
      apply hi
      exact h i

end PTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace PTree

private theorem gsident_tree'_proof {A : Type} (i : positive) (m : tree' A) {v : A} :
    get' i m = some v → set' i v m = m := by
  induction m generalizing i v <;> cases i <;> simp_all [get', set']

theorem gsident : gsidentStatement := by
  intro A i m v h
  cases m with
  | Empty => simp [get] at h
  | Nodes m =>
      simp only [get, set] at h ⊢
      rw [gsident_tree'_proof i m h]

end PTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace PTree

private theorem set'_set0_set2_proof {A : Type} (i : positive) (x y : A) :
    set' i y (set0 i x) = set0 i y := by
  induction i with
  | xH => rfl
  | xO i ih => simpa [set0, set'] using congrArg Node100 ih
  | xI i ih => simpa [set0, set'] using congrArg Node001 ih

private theorem set'_set2_proof {A : Type} (i : positive) (x y : A) (m : tree' A) :
    set' i y (set' i x m) = set' i y m := by
  induction i generalizing m with
  | xH => cases m <;> rfl
  | xO i ih =>
      cases m with
      | Node001 r => simpa [set'] using
          (congrArg (fun l => Node101 l r) (set'_set0_set2_proof i x y))
      | Node010 z => simpa [set'] using
          (congrArg (fun l => Node110 l z) (set'_set0_set2_proof i x y))
      | Node011 z r => simpa [set'] using
          (congrArg (fun l => Node111 l z r) (set'_set0_set2_proof i x y))
      | Node100 l => simpa [set'] using congrArg Node100 (ih l)
      | Node101 l r => simpa [set'] using congrArg (fun l => Node101 l r) (ih l)
      | Node110 l z => simpa [set'] using congrArg (fun l => Node110 l z) (ih l)
      | Node111 l z r => simpa [set'] using congrArg (fun l => Node111 l z r) (ih l)
  | xI i ih =>
      cases m with
      | Node001 r => simpa [set'] using congrArg Node001 (ih r)
      | Node010 z => simpa [set'] using
          (congrArg (fun r => Node011 z r) (set'_set0_set2_proof i x y))
      | Node011 z r => simpa [set'] using congrArg (fun r => Node011 z r) (ih r)
      | Node100 l => simpa [set'] using
          (congrArg (fun r => Node101 l r) (set'_set0_set2_proof i x y))
      | Node101 l r => simpa [set'] using congrArg (fun r => Node101 l r) (ih r)
      | Node110 l z => simpa [set'] using
          (congrArg (fun r => Node111 l z r) (set'_set0_set2_proof i x y))
      | Node111 l z r => simpa [set'] using congrArg (fun r => Node111 l z r) (ih r)

theorem set2 : set2Statement := by
  intro A i m v1 v2
  cases m with
  | Empty => simpa [set] using congrArg Nodes (set'_set0_set2_proof i v1 v2)
  | Nodes m => simpa [set] using congrArg Nodes (set'_set2_proof i v1 v2 m)

end PTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace PTree

private def beqOptBool_pg {A : Type} (beqA : A → A → Bool) :
    Option A → Option A → Bool
  | none, none => true
  | some a₁, some a₂ => beqA a₁ a₂
  | _, _ => false

private theorem bool_and_true_pg {a b : Bool} (h : a && b = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem beqNode_pg {A : Type} (beqA : A → A → Bool)
    (l₁ : PTree.t A) (o₁ : Option A) (r₁ : PTree.t A)
    (l₂ : PTree.t A) (o₂ : Option A) (r₂ : PTree.t A)
    (h₁ : PTree.not_trivially_empty l₁ o₁ r₁)
    (h₂ : PTree.not_trivially_empty l₂ o₂ r₂) :
    PTree.beq beqA (PTree.Node l₁ o₁ r₁) (PTree.Node l₂ o₂ r₂) =
      ((PTree.beq beqA l₁ l₂ && beqOptBool_pg beqA o₁ o₂) &&
        PTree.beq beqA r₁ r₂) := by
  cases l₁ <;> cases o₁ <;> cases r₁ <;>
    cases l₂ <;> cases o₂ <;> cases r₂ <;>
      simp_all [PTree.Node, PTree.not_trivially_empty, PTree.beq,
        PTree.beq', beqOptBool_pg, Bool.and_assoc, Bool.and_left_comm,
        Bool.and_comm]

private theorem nodeWitness_pg {A : Type} (l : PTree.t A) (o : Option A)
    (r : PTree.t A) (h : PTree.not_trivially_empty l o r) :
    ∃ p v, PTree.get p (PTree.Node l o r) = some v := by
  have hne : PTree.Node l o r ≠ .Empty := by
    intro hn
    cases l <;> cases o <;> cases r <;>
      simp_all [PTree.Node, PTree.not_trivially_empty]
  cases hnode : PTree.Node l o r with
  | Empty => exact (hne hnode).elim
  | Nodes m =>
      rcases PTree.tree'_not_empty m with ⟨p, hp⟩
      cases hm : PTree.get' p m with
      | none => exact (hp hm).elim
      | some v => exact ⟨p, v, by simpa [hnode, PTree.get] using hm⟩

private theorem getNodeAt_pg {A : Type} (i : positive) (l : PTree.t A)
    (o : Option A) (r : PTree.t A) :
    PTree.get i (PTree.Node l o r) =
      match i with
      | .xH => o
      | .xO p => PTree.get p l
      | .xI p => PTree.get p r := by
  cases i <;> cases l <;> cases o <;> cases r <;> rfl

end PTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace PTree

private theorem beq_true_pointwise_pg {A : Type} (beqA : A → A → Bool) :
    ∀ (m₁ m₂ : PTree.t A),
      PTree.beq beqA m₁ m₂ = true →
        ∀ x, beqOptBool_pg beqA (PTree.get x m₁) (PTree.get x m₂) = true := by
  intro m₁ m₂ h
  cases m₁ with
  | Empty =>
      cases m₂ with
      | Empty => intro x; simp [beqOptBool_pg, PTree.get]
      | Nodes m₂ => simp [PTree.beq] at h
  | Nodes m₁ =>
      cases m₂ with
      | Empty => simp [PTree.beq] at h
      | Nodes m₂ =>
          induction m₁ generalizing m₂ with
          | Node001 r ih =>
              cases m₂ with
              | Node001 r₂ =>
                  simp only [PTree.beq, PTree.beq'] at h
                  intro x
                  cases x with
                  | xH => simp [beqOptBool_pg, PTree.get, PTree.get']
                  | xO q => simp [beqOptBool_pg, PTree.get, PTree.get']
                  | xI q => simpa [beqOptBool_pg, PTree.get, PTree.get'] using ih r₂ h q
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node010 x₁ =>
              cases m₂ with
              | Node010 x₂ =>
                  have hx : beqA x₁ x₂ = true := by
                    simpa [PTree.beq, PTree.beq'] using h
                  intro x
                  cases x with
                  | xH => simpa [beqOptBool_pg, PTree.get, PTree.get'] using hx
                  | xO q => simp [beqOptBool_pg, PTree.get, PTree.get']
                  | xI q => simp [beqOptBool_pg, PTree.get, PTree.get']
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node011 x₁ r ih =>
              cases m₂ with
              | Node011 x₂ r₂ =>
                  have hparts := bool_and_true_pg (by simpa [PTree.beq, PTree.beq'] using h)
                  have hx : beqA x₁ x₂ = true := hparts.1
                  have hr : PTree.beq beqA (.Nodes r) (.Nodes r₂) = true := by
                    simpa [PTree.beq, PTree.beq'] using hparts.2
                  intro x
                  cases x with
                  | xH => simpa [beqOptBool_pg, PTree.get, PTree.get'] using hx
                  | xO q => simp [beqOptBool_pg, PTree.get, PTree.get']
                  | xI q => simpa [beqOptBool_pg, PTree.get, PTree.get'] using ih r₂ hr q
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node100 l ih =>
              cases m₂ with
              | Node100 l₂ =>
                  have hl : PTree.beq beqA (.Nodes l) (.Nodes l₂) = true := by
                    simpa [PTree.beq, PTree.beq'] using h
                  intro x
                  cases x with
                  | xH => simp [beqOptBool_pg, PTree.get, PTree.get']
                  | xO q => simpa [beqOptBool_pg, PTree.get, PTree.get'] using ih l₂ hl q
                  | xI q => simp [beqOptBool_pg, PTree.get, PTree.get']
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node101 l r ihl ihr =>
              cases m₂ with
              | Node101 l₂ r₂ =>
                  have hparts := bool_and_true_pg (by simpa [PTree.beq, PTree.beq'] using h)
                  have hl : PTree.beq beqA (.Nodes l) (.Nodes l₂) = true := by
                    simpa [PTree.beq, PTree.beq'] using hparts.1
                  have hr : PTree.beq beqA (.Nodes r) (.Nodes r₂) = true := by
                    simpa [PTree.beq, PTree.beq'] using hparts.2
                  intro x
                  cases x with
                  | xH => simp [beqOptBool_pg, PTree.get, PTree.get']
                  | xO q => simpa [beqOptBool_pg, PTree.get, PTree.get'] using ihl l₂ hl q
                  | xI q => simpa [beqOptBool_pg, PTree.get, PTree.get'] using ihr r₂ hr q
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node110 l x₁ ih =>
              cases m₂ with
              | Node110 l₂ x₂ =>
                  have hparts := bool_and_true_pg (by simpa [PTree.beq, PTree.beq'] using h)
                  have hx : beqA x₁ x₂ = true := hparts.1
                  have hl : PTree.beq beqA (.Nodes l) (.Nodes l₂) = true := by
                    simpa [PTree.beq, PTree.beq'] using hparts.2
                  intro x
                  cases x with
                  | xH => simpa [beqOptBool_pg, PTree.get, PTree.get'] using hx
                  | xO q => simpa [beqOptBool_pg, PTree.get, PTree.get'] using ih l₂ hl q
                  | xI q => simp [beqOptBool_pg, PTree.get, PTree.get']
              | _ => simp [PTree.beq, PTree.beq'] at h
          | Node111 l x₁ r ihl ihr =>
              cases m₂ with
              | Node111 l₂ x₂ r₂ =>
                  have hbool :
                      (beqA x₁ x₂ && PTree.beq' beqA l l₂) &&
                        PTree.beq' beqA r r₂ = true := by
                    simpa [PTree.beq, PTree.beq'] using h
                  have hparts₁ := bool_and_true_pg hbool
                  have hleft : (beqA x₁ x₂ && PTree.beq' beqA l l₂) = true := hparts₁.1
                  have hparts₂ : beqA x₁ x₂ = true ∧ PTree.beq' beqA l l₂ = true :=
                    by
                      cases hA : beqA x₁ x₂ with
                      | false => simp [hA] at hleft
                      | true =>
                          cases hL : PTree.beq' beqA l l₂ with
                          | false => simp [hA, hL] at hleft
                          | true => exact ⟨rfl, rfl⟩
                  have hx : beqA x₁ x₂ = true := hparts₂.1
                  have hl : PTree.beq beqA (.Nodes l) (.Nodes l₂) = true := by
                    simpa [PTree.beq, PTree.beq'] using hparts₂.2
                  have hr : PTree.beq beqA (.Nodes r) (.Nodes r₂) = true := by
                    simpa [PTree.beq, PTree.beq'] using hparts₁.2
                  intro x
                  cases x with
                  | xH => simpa [beqOptBool_pg, PTree.get, PTree.get'] using hx
                  | xO q => simpa [beqOptBool_pg, PTree.get, PTree.get'] using ihl l₂ hl q
                  | xI q => simpa [beqOptBool_pg, PTree.get, PTree.get'] using ihr r₂ hr q
              | _ => simp [PTree.beq, PTree.beq'] at h

end PTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace PTree

private theorem extensional_beq_true_pg {A : Type} (beqA : A → A → Bool) :
    ∀ (m₁ m₂ : PTree.t A),
      (∀ x, beqOptBool_pg beqA (PTree.get x m₁) (PTree.get x m₂) = true) →
        PTree.beq beqA m₁ m₂ = true := by
  intro m₁
  have hP : PLift (∀ m₂ : PTree.t A,
      (∀ x, beqOptBool_pg beqA (PTree.get x m₁) (PTree.get x m₂) = true) →
        PTree.beq beqA m₁ m₂ = true) := by
    refine PTree.tree_ind
        (P := fun m₁ => PLift (∀ m₂ : PTree.t A,
          (∀ x, beqOptBool_pg beqA (PTree.get x m₁) (PTree.get x m₂) = true) →
            PTree.beq beqA m₁ m₂ = true)) ?_ ?_ m₁
    · refine ⟨?_⟩
      intro m₂ H
      cases m₂ with
      | Empty => rfl
      | Nodes m₂ =>
          rcases PTree.tree'_not_empty m₂ with ⟨p, hp⟩
          cases hm : PTree.get' p m₂ with
          | none => exact (hp hm).elim
          | some v =>
              have hx := H p
              simp [PTree.get, hm, beqOptBool_pg] at hx
    · intro l il o r ir hne
      refine ⟨?_⟩
      intro m₂
      have hP₂ : PLift (
          (∀ x, beqOptBool_pg beqA (PTree.get x (PTree.Node l o r))
              (PTree.get x m₂) = true) →
            PTree.beq beqA (PTree.Node l o r) m₂ = true) := by
        refine PTree.tree_ind
            (P := fun m₂ => PLift (
              (∀ x, beqOptBool_pg beqA (PTree.get x (PTree.Node l o r))
                  (PTree.get x m₂) = true) →
                PTree.beq beqA (PTree.Node l o r) m₂ = true)) ?_ ?_ m₂
        · refine ⟨?_⟩
          intro H
          rcases nodeWitness_pg l o r hne with ⟨p, v, hv⟩
          have hx := H p
          rw [hv] at hx
          simpa [PTree.get, beqOptBool_pg] using hx
        · intro l₂ il₂ o₂ r₂ ir₂ hne₂
          refine ⟨?_⟩
          intro H
          have hleft : ∀ p,
              beqOptBool_pg beqA (PTree.get p l) (PTree.get p l₂) = true := by
            intro p
            have hx := H (.xO p)
            rw [getNodeAt_pg (.xO p) l o r,
              getNodeAt_pg (.xO p) l₂ o₂ r₂] at hx
            simpa [beqOptBool_pg] using hx
          have hroot : beqOptBool_pg beqA o o₂ = true := by
            have hx := H .xH
            rw [getNodeAt_pg .xH l o r,
              getNodeAt_pg .xH l₂ o₂ r₂] at hx
            simpa [beqOptBool_pg] using hx
          have hright : ∀ p,
              beqOptBool_pg beqA (PTree.get p r) (PTree.get p r₂) = true := by
            intro p
            have hx := H (.xI p)
            rw [getNodeAt_pg (.xI p) l o r,
              getNodeAt_pg (.xI p) l₂ o₂ r₂] at hx
            simpa [beqOptBool_pg] using hx
          have hleft_beq := PLift.down il l₂ hleft
          have hright_beq := PLift.down ir r₂ hright
          rw [beqNode_pg beqA l o r l₂ o₂ r₂ hne hne₂]
          simp [hleft_beq, hroot, hright_beq]
      exact PLift.down hP₂
  exact PLift.down hP

theorem beq_correct_bool : beq_correct_boolStatement := by
  intro A beqA m₁ m₂
  change PTree.beq beqA m₁ m₂ = true ↔
    ∀ x, beqOptBool_pg beqA (PTree.get x m₁) (PTree.get x m₂) = true
  constructor
  · exact beq_true_pointwise_pg beqA m₁ m₂
  · exact extensional_beq_true_pg beqA m₁ m₂

end PTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace PTree

theorem prev_append_prev : prev_append_prevStatement := by
  intro i j
  induction i generalizing j with
  | xH => rfl
  | xI i ih =>
      change prev (prev_append i (xI j)) = prev_append j (xI i)
      rw [ih (xI j)]
      rfl
  | xO i ih =>
      change prev (prev_append i (xO j)) = prev_append j (xO i)
      rw [ih (xO j)]
      rfl

theorem prev_append_inj : prev_append_injStatement := by
  intro i
  induction i with
  | xH =>
      intro j j' h
      exact h
  | xI i ih =>
      intro j j' h
      have h' : xI j = xI j' := ih (xI j) (xI j') (by simpa [prev_append] using h)
      cases h'
      rfl
  | xO i ih =>
      intro j j' h
      have h' : xO j = xO j' := ih (xO j) (xO j') (by simpa [prev_append] using h)
      cases h'
      rfl

theorem beq_correct_proof : beq_correctStatement := by
  intro A beqA m₁ m₂
  change PTree.beq beqA m₁ m₂ = true ↔
    ∀ x : elt,
      match PTree.get x m₁, PTree.get x m₂ with
      | none, none => True
      | some y₁, some y₂ => beqA y₁ y₂ = true
      | _, _ => False
  rw [beq_correct_bool]
  constructor <;> intro h x
  · have hx := h x
    cases h₁ : PTree.get x m₁ with
    | none =>
        cases h₂ : PTree.get x m₂ with
        | none => trivial
        | some y₂ => simp [beqOptBool_pg, h₁, h₂] at hx
    | some y₁ =>
        cases h₂ : PTree.get x m₂ with
        | none => simp [beqOptBool_pg, h₁, h₂] at hx
        | some y₂ => simpa [h₁, h₂] using hx
  · have hx := h x
    cases h₁ : PTree.get x m₁ with
    | none =>
        cases h₂ : PTree.get x m₂ with
        | none => rfl
        | some y₂ => exact (by simpa [h₁, h₂] using hx : False).elim
    | some y₁ =>
        cases h₂ : PTree.get x m₂ with
        | none => exact (by simpa [h₁, h₂] using hx : False).elim
        | some y₂ => simpa [h₁, h₂] using hx

end PTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

namespace PTree

theorem gmap' : gmap'Statement := by
  intro A B f i j m
  induction i generalizing j m with
  | xH =>
      cases m <;> rfl
  | xO i ih =>
      cases m with
      | Node001 r => rfl
      | Node010 x => rfl
      | Node011 x r => rfl
      | Node100 l =>
          simpa [map', get', prev_append] using ih (.xO j) l
      | Node101 l r =>
          simpa [map', get', prev_append] using ih (.xO j) l
      | Node110 l x =>
          simpa [map', get', prev_append] using ih (.xO j) l
      | Node111 l x r =>
          simpa [map', get', prev_append] using ih (.xO j) l
  | xI i ih =>
      cases m with
      | Node001 r =>
          simpa [map', get', prev_append] using ih (.xI j) r
      | Node010 x => rfl
      | Node011 x r =>
          simpa [map', get', prev_append] using ih (.xI j) r
      | Node100 l => rfl
      | Node101 l r =>
          simpa [map', get', prev_append] using ih (.xI j) r
      | Node110 l x => rfl
      | Node111 l x r =>
          simpa [map', get', prev_append] using ih (.xI j) r

theorem gmap : gmapStatement := by
  intro A B f i m
  cases m with
  | Empty => rfl
  | Nodes m =>
      change get' i (map' f m .xH) =
        Option.map (f i) (get' i m)
      rw [gmap']
      change Option.map (f (prev (prev i))) (get' i m) =
        Option.map (f i) (get' i m)
      rw [prev_involutive]

theorem gmap1 : gmap1Statement := by
  intro A B f i m
  cases m with
  | Empty => rfl
  | Nodes m =>
      induction m generalizing i with
      | Node001 r ih =>
          cases i with
          | xH => rfl
          | xO q => rfl
          | xI q => exact ih q
      | Node010 x =>
          cases i <;> rfl
      | Node011 x r ih =>
          cases i with
          | xH => rfl
          | xO q => rfl
          | xI q => exact ih q
      | Node100 l ih =>
          cases i with
          | xH => rfl
          | xO q => exact ih q
          | xI q => rfl
      | Node101 l r ihl ihr =>
          cases i with
          | xH => rfl
          | xO q => exact ihl q
          | xI q => exact ihr q
      | Node110 l x ih =>
          cases i with
          | xH => rfl
          | xO q => exact ih q
          | xI q => rfl
      | Node111 l x r ihl ihr =>
          cases i with
          | xH => rfl
          | xO q => exact ihl q
          | xI q => exact ihr q

theorem gmap_filter1 : gmap_filter1Statement := by
  intro A B f m i
  rw [get_map_filter1_proof]
  cases h : get i m <;> simp [h, Option.bind]

end PTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

namespace PTree

theorem xelements'_append : xelements'_appendStatement := by
  intro A m i k1 k2
  exact xelements'_append_equation m i k1 k2

theorem xelements_Node : xelements_NodeStatement := by
  intro A l o r i
  cases l <;> cases o <;> cases r <;>
    simp [Node, xelements, xelements']
  all_goals
    rw [← xelements'_append_equation]
    simp

theorem xelements_correct : xelements_correctStatement := by
  intro A m i j v h
  cases m with
  | Empty => simp [get] at h
  | Nodes m' =>
      have h' : get' i m' = some v := by simpa [get] using h
      have hc := get_xelements'_correct m' i j v [] h'
      simpa [xelements] using hc

theorem in_xelements : in_xelementsStatement := by
  intro A m i k v h
  cases m with
  | Empty => simp [xelements] at h
  | Nodes m' =>
      have h' : (k, v) ∈ xelements' m' i [] := by
        simpa [xelements] using h
      rcases in_xelements'_complete m' i (k, v) h' with ⟨j, hk, hget⟩
      refine ⟨j, hk, ?_⟩
      simpa [get] using hget

end PTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps
namespace PTree

theorem xkeys_Node : xkeys_NodeStatement := by
  intro A m1 o m2 i
  change tree A at m1
  change tree A at m2
  change (xelements (Node m1 o m2) i).map Prod.fst =
    (xelements m1 (.xO i)).map Prod.fst ++
      (match o with | none => [] | some _ => [prev i]) ++
      (xelements m2 (.xI i)).map Prod.fst
  rw [xelements_Node]
  simp only [List.map_append, List.map_cons, List.map_nil]
  cases o <;> simp

theorem in_xkeys : in_xkeysStatement := by
  intro A m i k h
  unfold xkeys at h
  rcases List.mem_map.mp h with ⟨p, hp, rfl⟩
  rcases in_xelements m i p.1 p.2 hp with ⟨j, hj, _⟩
  exact ⟨j, hj⟩

private theorem list_norepet_of_nodup {A : Type} :
    ∀ l : List A, l.Nodup → list_norepet l := by
  intro l h
  induction l with
  | nil => exact CompCert4Lean.Lib.Coqlib.list_norepet.nil _
  | cons a l ih =>
      have hc := List.nodup_cons.mp h
      exact CompCert4Lean.Lib.Coqlib.list_norepet.cons a hc.1 (ih hc.2)

theorem xelements_keys_norepet : xelements_keys_norepetStatement := by
  intro A m i
  cases m with
  | Empty => exact CompCert4Lean.Lib.Coqlib.list_norepet.nil _
  | Nodes m' =>
      apply list_norepet_of_nodup
      simpa [xkeys, xelements] using (keys_nodup_xelements' m' i)

theorem elements_keys_norepet : elements_keys_norepetStatement := by
  intro A m
  change list_norepet (xkeys m .xH)
  exact xelements_keys_norepet m .xH

end PTree
end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

namespace PTree

private theorem list_forall2_append_local {A B : Type} {P : A → B → Prop}
    {a1 : List A} {b1 : List B} {a2 : List A} {b2 : List B} :
      list_forall2 P a1 b1 → list_forall2 P a2 b2 →
        list_forall2 P (a1 ++ a2) (b1 ++ b2) := by
  intro h1
  induction h1 with
  | nil =>
      intro h2
      simpa using h2
  | cons a1 b1 hp ht ih =>
      intro h2
      simp only [List.cons_append]
      exact CompCert4Lean.Lib.Coqlib.list_forall2.cons a1 b1 hp (ih h2)

private theorem elements_canonical_order'_aux {A B : Type} (R : A → B → Prop) :
    ∀ (m : tree A) (i : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
      (n : tree B),
      (∀ j, option_rel R (get j m) (get j n)) →
      list_forall2 (fun p q => p.1 = q.1 ∧ R p.2 q.2)
        (xelements m i) (xelements n i) := by
  intro m
  have hP : PLift (∀ (i : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
      (n : tree B),
      (∀ j, option_rel R (get j m) (get j n)) →
      list_forall2 (fun p q => p.1 = q.1 ∧ R p.2 q.2)
        (xelements m i) (xelements n i)) := by
    refine tree_ind
        (P := fun m => PLift (∀ (i : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
          (n : tree B),
          (∀ j, option_rel R (get j m) (get j n)) →
          list_forall2 (fun p q => p.1 = q.1 ∧ R p.2 q.2)
            (xelements m i) (xelements n i))) ?_ ?_ m
    · refine ⟨?_⟩
      intro i n REL
      cases n with
      | Empty => exact list_forall2_nil _
      | Nodes n' =>
          have hnone : ∀ j, get j (.Nodes n' : tree B) = none := by
            intro j
            cases h : get j (.Nodes n' : tree B) with
            | none => rfl
            | some y =>
                have hget : get' j n' = some y := by
                  simpa [get] using h
                have h' : option_rel R none (get' j n') := by
                  have hrel := REL j
                  change option_rel R none (get' j n') at hrel
                  exact hrel
                rw [hget] at h'
                cases h'
          have hn : (.Nodes n' : tree B) = .Empty :=
            extensionality_empty _ hnone
          cases hn
    · intro l ihl o r ihr hne
      refine ⟨?_⟩
      intro i n
      have hP₂ : PLift (
          (∀ j, option_rel R (get j (Node l o r)) (get j n)) →
          list_forall2 (fun p q => p.1 = q.1 ∧ R p.2 q.2)
            (xelements (Node l o r) i) (xelements n i)) := by
        refine tree_ind
          (P := fun n => PLift (
            (∀ j, option_rel R (get j (Node l o r)) (get j n)) →
            list_forall2 (fun p q => p.1 = q.1 ∧ R p.2 q.2)
              (xelements (Node l o r) i) (xelements n i))) ?_ ?_ n
        · refine ⟨?_⟩
          intro REL
          have hmnone : ∀ j, get j (Node l o r) = none := by
            intro j
            cases h : get j (Node l o r) with
            | none => rfl
            | some x =>
                have h' : option_rel R (some x) none := by
                  have hrel := REL j
                  rw [h] at hrel
                  simpa [get] using hrel
                cases h'
          have hm : Node l o r = (.Empty : tree A) :=
            extensionality_empty _ hmnone
          have hne' : Node l o r ≠ (.Empty : tree A) := by
            intro hzero
            cases l <;> cases o <;> cases r <;>
              simp_all [Node, not_trivially_empty]
          exact (hne' hm).elim
        · intro l2 ihl2 o2 r2 ihr2 hne2
          refine ⟨?_⟩
          intro REL
          have hleft : ∀ j, option_rel R (get j l) (get j l2) := by
            intro j
            have h := REL (.xO j)
            rw [gNode_proof, gNode_proof] at h
            simpa using h
          have hroot : option_rel R o o2 := by
            have h := REL .xH
            rw [gNode_proof, gNode_proof] at h
            simpa using h
          have hright : ∀ j, option_rel R (get j r) (get j r2) := by
            intro j
            have h := REL (.xI j)
            rw [gNode_proof, gNode_proof] at h
            simpa using h
          have hl := PLift.down ihl (xO i) l2 hleft
          have hr := PLift.down ihr (xI i) r2 hright
          have hmid :
              list_forall2 (fun p q => p.1 = q.1 ∧ R p.2 q.2)
                (match o with | none => [] | some x => [(prev i, x)])
                (match o2 with | none => [] | some y => [(prev i, y)]) := by
            cases hroot with
            | none => exact list_forall2_nil _
            | some x y hxy =>
                exact CompCert4Lean.Lib.Coqlib.list_forall2.cons _ _ ⟨rfl, hxy⟩
                  (list_forall2_nil _)
          rw [xelements_Node, xelements_Node]
          exact list_forall2_append_local
            (list_forall2_append_local hl hmid) hr
      exact PLift.down hP₂
  exact PLift.down hP

theorem elements_canonical_order' : elements_canonical_order'Statement := by
  intro A B R m n REL
  exact elements_canonical_order'_aux R m
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.xH n REL

theorem elements_canonical_order : elements_canonical_orderStatement := by
  intro A B R m n hmn hnm
  apply elements_canonical_order'
  intro i
  cases hm : get i m with
  | none =>
      cases hn : get i n with
      | none => exact option_rel.none R
      | some y =>
          rcases hnm i y (by simpa [hn]) with ⟨x, hx, hxy⟩
          have hfalse : False := by
            simpa [hm] using hx
          exact hfalse.elim
  | some x =>
      cases hn : get i n with
      | none =>
          rcases hmn i x (by simpa [hm]) with ⟨y, hy, hxy⟩
          have hfalse : False := by
            simpa [hn] using hy
          exact hfalse.elim
      | some y =>
          rcases hmn i x (by simpa [hm]) with ⟨y', hy', hxy⟩
          have hyy : y' = y := (Option.some.inj (by simpa [hn] using hy')).symm
          subst y'
          exact option_rel.some x y hxy

theorem fold'_xelements' : fold'_xelements'Statement := by
  intro A B f m i v l
  induction m generalizing i v l <;>
    simp_all [fold', xelements', List.foldl, List.foldl_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals rw [foldl_step']
  all_goals simp_all [List.foldl_append]

end PTree

namespace PMap

theorem gi : giStatement := by
  intro A i x
  rfl

end PMap

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

namespace PMap

theorem gss : gssStatement := by
  intro A i x m
  cases m with
  | mk d tree =>
      have hget : PTree.get i (PTree.set i x tree) = some x :=
        PTree.gss (A := A) i x tree
      simp [hget, get, set]

theorem gso : gsoStatement := by
  intro A i j x m hij
  cases m with
  | mk d tree =>
      have hget : PTree.get i (PTree.set j x tree) = PTree.get i tree :=
        PTree.gso (A := A) (i := i) (j := j) x tree hij
      simp [hget, get, set]

theorem gsspec : gsspecStatement := by
  intro A i j x m
  cases h : CompCert4Lean.Lib.Coqlib.peq i j with
  | left hij =>
      subst j
      simpa [h] using (gss (A := A) i x m)
  | right hne =>
      simpa [h] using (gso (A := A) (i := i) (j := j) x m hne)

theorem gmap_proof : gmapStatement := by
  intro A B f i m
  cases m with
  | mk d tree =>
      have hmap : PTree.get i (PTree.map1 f tree) = Option.map f (PTree.get i tree) :=
        PTree.gmap1 f i tree
      simp [hmap, map, get]
      cases h : PTree.get i tree <;> simp [h]

end PMap

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

namespace PMap

theorem set2 : set2Statement := by
  intro A i x y m
  cases m with
  | mk d tree =>
      simp only [set]
      exact congrArg (fun tr => (d, tr)) (PTree.set2 (A := A) i tree x y)

end PMap

namespace ZMap

theorem gi_proof : gi := by
  intro A x i
  exact PMap.gi (A := A) (ZIndexed.index i) x

theorem gss_proof : gss := by
  intro A i x m
  exact PMap.gss (A := A) (ZIndexed.index i) x m

theorem gso_proof : gso := by
  intro A i j x m hij
  apply PMap.gso (A := A) (i := ZIndexed.index i) (j := ZIndexed.index j) x m
  intro heq
  apply hij
  exact ZIndexed.index_inj i j heq

end ZMap

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

namespace ZMap

theorem gsspec_proof : gsspec := by
  intro A i j x m
  cases h : elt_eq i j with
  | left hij =>
      subst j
      simpa [h] using (PMap.gss (A := A) (ZIndexed.index i) x m)
  | right hne =>
      have hindex : ZIndexed.index i ≠ ZIndexed.index j := by
        intro heq
        apply hne
        exact ZIndexed.index_inj i j heq
      simpa [h] using
        (PMap.gso (A := A) (i := ZIndexed.index i) (j := ZIndexed.index j)
          x m hindex)

end ZMap

namespace ZTree

theorem gso_proof : gso := by
  intro A i j x m hij
  apply PTree.gso (A := A) (i := ZIndexed.index i) (j := ZIndexed.index j) x m
  intro heq
  apply hij
  exact ZIndexed.index_inj i j heq

theorem grs_proof : grs := by
  intro A i m
  exact PTree.grs_proof (A := A) (ZIndexed.index i) m

theorem gro_proof : gro := by
  intro A i j m hij
  apply PTree.gro_proof (A := A) (i := ZIndexed.index i) (j := ZIndexed.index j) m
  intro heq
  · apply hij
    exact ZIndexed.index_inj i j heq

end ZTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

namespace PTree_Properties

private theorem nodup_of_list_norepet {A : Type} :
    ∀ (l : List A), PTree.list_norepet l → l.Nodup := by
  intro l h
  induction h with
  | nil => exact List.nodup_nil
  | cons hd hnot htail ih =>
      exact List.nodup_cons.mpr ⟨hnot, ih⟩

theorem of_list_norepet_proof : of_list_norepet := by
  intro A l k v hnr hmem
  have hnodup : (l.map Prod.fst).Nodup :=
    nodup_of_list_norepet _ hnr
  change PTree.get k (set_list (PTree.empty A) l) = some v
  exact get_set_list_some (PTree.empty A) l k v hnodup hmem

end PTree_Properties

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

namespace PTree_Properties

noncomputable def fold_ind_proof : fold_ind := by
  intro V A f P init mFinal hbase hrec
  have hnodup_of_norepet : ∀ {X : Type} (l : List X),
      PTree.list_norepet l → l.Nodup := by
    intro X l h
    induction h with
    | nil => exact List.nodup_nil
    | cons hd hnot htail ih =>
        exact List.nodup_cons.mpr ⟨hnot, ih⟩
  have hnorepet_reverse : ∀ {X : Type} (l : List X),
      PTree.list_norepet l → PTree.list_norepet l.reverse := by
    intro X l h
    have hn : l.Nodup := hnodup_of_norepet l h
    have hnr : l.reverse.Nodup := by
      apply List.pairwise_reverse.mpr
      exact hn.imp (by
        intro a b hab hba
        exact hab hba.symm)
    have hnorepet_of_nodup : ∀ {Y : Type} (xs : List Y),
        xs.Nodup → PTree.list_norepet xs := by
      intro Y xs hx
      induction xs with
      | nil => exact CompCert4Lean.Lib.Coqlib.list_norepet.nil _
      | cons hd tl ih =>
          have hc := List.nodup_cons.mp hx
          exact CompCert4Lean.Lib.Coqlib.list_norepet.cons hd hc.1 (ih hc.2)
    exact hnorepet_of_nodup _ hnr
  have hprocess : ∀ (l : List (PTree.elt × V)),
      (∀ k v, (k, v) ∈ l → PTree.get k mFinal = some v) →
      PTree.list_norepet (l.map Prod.fst) →
      (∀ m, (∀ k v, (k, v) ∈ l ↔ PTree.get k m = some v) →
        Nonempty (P m (List.foldr (fun p a => f a p.1 p.2) init l))) := by
    intro l
    induction l with
    | nil =>
        intro hfinal hnr m heq
        apply Nonempty.intro
        apply hbase m
        intro k
        cases hget : PTree.get k m with
        | none => rfl
        | some v =>
            have hmem : (k, v) ∈ ([] : List (PTree.elt × V)) :=
              (heq k v).mpr hget
            cases hmem
    | cons p l ih =>
        rcases p with ⟨k, v⟩
        intro hfinal hnr m heq
        have hnr' : PTree.list_norepet (k :: l.map Prod.fst) := by
          simpa using hnr
        cases hnr' with
        | cons _ hnot htail =>
            have hfinalhead : PTree.get k mFinal = some v := by
              apply hfinal k v
              simp
            have hgethead : PTree.get k m = some v := by
              apply (heq k v).mp
              simp
            have hrest : ∀ k' v', (k', v') ∈ l ↔
                PTree.get k' (PTree.remove k m) = some v' := by
              intro k' v'
              cases hEq : PTree.elt_eq k' k with
              | left hEq' =>
                  subst k'
                  have hzero : PTree.get k (PTree.remove k m) = none :=
                    PTree.grs_proof (A := V) k m
                  constructor
                  · intro hmem
                    exfalso
                    apply hnot
                    exact List.mem_map.mpr ⟨(k, v'), hmem, rfl⟩
                  · intro hget
                    rw [hzero] at hget
                    cases hget
              | right hne =>
                  have hgr : PTree.get k' (PTree.remove k m) = PTree.get k' m :=
                    PTree.gro_proof (A := V) (i := k') (j := k) m hne
                  constructor
                  · intro hmem
                    have hmget : PTree.get k' m = some v' :=
                      (heq k' v').mp (by simp [hmem])
                    exact hgr.trans hmget
                  · intro hget
                    have hmget : PTree.get k' m = some v' := hgr.symm.trans hget
                    have hmemfull : (k', v') ∈ (k, v) :: l :=
                      (heq k' v').mpr hmget
                    simp only [List.mem_cons] at hmemfull
                    rcases hmemfull with hhead | htail
                    · cases hhead
                      exact (hne rfl).elim
                    · exact htail
            have hPm : Nonempty (P (PTree.remove k m)
                (List.foldr (fun p a => f a p.1 p.2) init l)) :=
              ih (by
                intro k' v' hmem
                exact hfinal k' v' (List.mem_cons_of_mem _ hmem)) htail
                (PTree.remove k m) hrest
            rcases hPm with ⟨ha⟩
            have hs := hrec m
              (List.foldr (fun (p : PTree.elt × V) (a : A) => f a p.1 p.2) init l)
              k v hgethead hfinalhead ha
            exact Nonempty.intro (by simpa [List.foldr] using hs)
  have hfinal_membership :
      ∀ k v, (k, v) ∈ (PTree.elements mFinal).reverse ↔
        PTree.get k mFinal = some v := by
    intro k v
    constructor
    · intro hmem
      apply PTree.elements_complete_proof (m := mFinal) k v
      exact List.mem_reverse.mp hmem
    · intro hget
      apply List.mem_reverse.mpr
      exact PTree.elements_correct_proof (m := mFinal) (i := k) hget
  have hnr_elements :
      PTree.list_norepet ((PTree.elements mFinal).reverse.map Prod.fst) := by
    simpa using
      (hnorepet_reverse (l := (PTree.elements mFinal).map Prod.fst)
        (PTree.elements_keys_norepet mFinal))
  have hp := hprocess (PTree.elements mFinal).reverse
    (by
      intro k v hmem
      exact (hfinal_membership k v).mp hmem)
    hnr_elements mFinal hfinal_membership
  have hfold := PTree.fold_spec_proof (A := V) (B := A) f init mFinal
  rw [hfold]
  rw [List.foldl_eq_foldr_reverse]
  exact Classical.choice hp

end PTree_Properties

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

namespace ZTree

theorem gss_proof : gss := by
  intro A i x m
  exact PTree.gss (A := A) (ZIndexed.index i) x m

theorem gcombine_proof : gcombine := by
  intro A B C f hnone m₁ m₂ i
  exact PTree.gcombine_proof (A := A) (B := B) (C := C) f hnone m₁ m₂
    (ZIndexed.index i)

end ZTree

end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps

namespace PTree_Properties

theorem in_of_list_proof : in_of_list := by
  have hrec : ∀ {A : Type} (k : PTree.elt) (v : A)
      (l : List (PTree.elt × A)) (m : PTree.t A),
      PTree.get k (List.foldl (fun m₀ kv => PTree.set kv.1 kv.2 m₀) m l) = some v →
        (k, v) ∈ l ∨ PTree.get k m = some v := by
    intro A k v l
    induction l with
    | nil =>
        intro m h
        change PTree.tree A at m
        right
        change PTree.get k m = some v at h
        exact h
    | cons p l ih =>
        rcases p with ⟨k₁, v₁⟩
        intro m h
        change PTree.tree A at m
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at k k₁
        change PTree.tree A at m
        have htail :
            PTree.get k
                (List.foldl (fun m₀ kv => PTree.set kv.1 kv.2 m₀)
                  (PTree.set k₁ v₁ m) l) = some v := by
          change PTree.get k
              (List.foldl (fun m₀ kv => PTree.set kv.1 kv.2 m₀)
                (PTree.set k₁ v₁ m) l) = some v at h
          exact h
        have hstep := ih (PTree.set k₁ v₁ m) htail
        rcases hstep with hmem | hget
        · left
          exact List.mem_cons_of_mem _ hmem
        · by_cases hkk : k = k₁
          · left
            subst k
            change PTree.get k₁ (PTree.set k₁ v₁ m) = some v at hget
            have hs : PTree.get k₁ (PTree.set k₁ v₁ m) = some v₁ :=
              PTree.gss (A := A) k₁ v₁ m
            have hv : v₁ = v := Option.some.inj (hs.symm.trans hget)
            exact List.mem_cons.mpr (Or.inl (Prod.ext rfl hv.symm))
          · right
            simpa [PTree.getSet_equation, hkk] using hget
  intro A l k v h
  have h' :
      PTree.get k
          (List.foldl (fun m₀ kv => PTree.set kv.1 kv.2 m₀)
            (PTree.empty A) l) = some v := by
    change PTree.get k
      (List.foldl (fun m₀ kv => PTree.set kv.1 kv.2 m₀)
        (PTree.empty A) l) = some v at h
    exact h
  have hres := hrec k v l (PTree.empty A) h'
  rcases hres with hmem | hget
  · exact hmem
  · have hempty : PTree.get k (PTree.empty A) = none := PTree.gempty A k
    rw [hempty] at hget
    cases hget

theorem of_list_dom_proof : of_list_dom := by
  have hrec : ∀ {A : Type} (k : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
      (l : List (CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive × A)) (m : PTree.tree A),
      k ∈ l.map Prod.fst ∨ (∃ v, PTree.get k m = some v) →
        ∃ v, PTree.get k
          (List.foldl (fun m₀ kv => PTree.set kv.1 kv.2 m₀) m l) = some v := by
    intro A k l
    induction l with
    | nil =>
        intro m h
        rcases h with hmem | ⟨v, hget⟩
        · cases hmem
        · exact ⟨v, hget⟩
    | cons p l ih =>
        rcases p with ⟨k₁, v₁⟩
        intro m h
        have htail :
            k ∈ l.map Prod.fst ∨
              (∃ v, PTree.get k (PTree.set k₁ v₁ m) = some v) := by
          rcases h with hmem | hbase
          · simp only [List.map_cons, List.mem_cons] at hmem
            rcases hmem with hEq | hmem
            · right
              subst k
              exact ⟨v₁, PTree.gss k₁ v₁ m⟩
            · left
              exact hmem
          · rcases hbase with ⟨v, hget⟩
            by_cases hEq : k = k₁
            · right
              subst k
              exact ⟨v₁, PTree.gss k₁ v₁ m⟩
            · right
              exact ⟨v, by
                simpa [PTree.getSet_equation, hEq] using hget⟩
        have hres := ih (PTree.set k₁ v₁ m) htail
        simpa [List.foldl] using hres
  intro A l k hmem
  have hres := hrec k l (PTree.empty A) (Or.inl hmem)
  change ∃ v, PTree.get k
    (List.foldl (fun m₀ kv => PTree.set kv.1 kv.2 m₀)
      (PTree.empty A) l) = some v
  exact hres

end PTree_Properties

end CompCert4Lean.Lib.Maps
namespace CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
namespace PTree

private theorem test_ext_tree'_proof {A : Type} :
    ∀ (m1 m2 : tree' A), (∀ i, get' i m1 = get' i m2) → m1 = m2 := by
  intro m1
  induction m1 with
  | Node001 r ih =>
      intro m2 h
      cases m2 with
      | Node001 r2 =>
          have hr : r = r2 := ih r2 (by intro i; exact h (.xI i))
          cases hr
          rfl
      | Node010 x => have hh := h .xH; simp [get'] at hh
      | Node011 x r2 => have hh := h .xH; simp [get'] at hh
      | Node100 l =>
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hh := h (.xO i); simp [get'] at hh
          exfalso
          exact hi hh.symm
      | Node101 l r2 =>
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hh := h (.xO i); simp [get'] at hh
          exfalso
          exact hi hh.symm
      | Node110 l x => have hh := h .xH; simp [get'] at hh
      | Node111 l x r2 => have hh := h .xH; simp [get'] at hh
  | Node010 x =>
      intro m2 h
      cases m2 with
      | Node001 r => have hh := h .xH; simp [get'] at hh
      | Node010 y =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          cases hxy; rfl
      | Node011 y r =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          rcases tree'_not_empty r with ⟨i, hi⟩
          have hx := h (.xI i); simp [get'] at hx
          exfalso
          exact hi hx.symm
      | Node100 l => have hh := h .xH; simp [get'] at hh
      | Node101 l r => have hh := h .xH; simp [get'] at hh
      | Node110 l y =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hx := h (.xO i); simp [get'] at hx
          exfalso
          exact hi hx.symm
      | Node111 l y r =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hx := h (.xO i); simp [get'] at hx
          exfalso
          exact hi hx.symm
  | Node011 x r ih =>
      intro m2 h
      cases m2 with
      | Node001 r2 => have hh := h .xH; simp [get'] at hh
      | Node010 y =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          rcases tree'_not_empty r with ⟨i, hi⟩
          have hx := h (.xI i); simp [get'] at hx
          exfalso
          exact hi hx
      | Node011 y r2 =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          have hr : r = r2 := ih r2 (by intro i; exact h (.xI i))
          cases hxy; cases hr; rfl
      | Node100 l => have hh := h .xH; simp [get'] at hh
      | Node101 l r2 => have hh := h .xH; simp [get'] at hh
      | Node110 l y =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hx := h (.xO i); simp [get'] at hx
          exfalso
          exact hi hx.symm
      | Node111 l y r2 =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hx := h (.xO i); simp [get'] at hx
          exfalso
          exact hi hx.symm
  | Node100 l ih =>
      intro m2 h
      cases m2 with
      | Node001 r =>
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hh := h (.xO i); simp [get'] at hh
          exfalso
          exact hi hh
      | Node010 x => have hh := h .xH; simp [get'] at hh
      | Node011 x r => have hh := h .xH; simp [get'] at hh
      | Node100 l2 =>
          have hl : l = l2 := ih l2 (by intro i; exact h (.xO i))
          cases hl; rfl
      | Node101 l2 r =>
          have hl : l = l2 := ih l2 (by intro i; exact h (.xO i))
          rcases tree'_not_empty r with ⟨i, hi⟩
          have hh := h (.xI i); simp [get'] at hh
          exfalso
          exact hi hh.symm
      | Node110 l2 x => have hh := h .xH; simp [get'] at hh
      | Node111 l2 x r => have hh := h .xH; simp [get'] at hh
  | Node101 l r ihl ihr =>
      intro m2 h
      cases m2 with
      | Node001 r2 =>
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hh := h (.xO i); simp [get'] at hh
          exfalso
          exact hi hh
      | Node010 x => have hh := h .xH; simp [get'] at hh
      | Node011 x r2 => have hh := h .xH; simp [get'] at hh
      | Node100 l2 =>
          have hl : l = l2 := ihl l2 (by intro i; exact h (.xO i))
          rcases tree'_not_empty r with ⟨i, hi⟩
          have hh := h (.xI i); simp [get'] at hh
          exfalso
          exact hi hh
      | Node101 l2 r2 =>
          have hl : l = l2 := ihl l2 (by intro i; exact h (.xO i))
          have hr : r = r2 := ihr r2 (by intro i; exact h (.xI i))
          cases hl; cases hr; rfl
      | Node110 l2 x => have hh := h .xH; simp [get'] at hh
      | Node111 l2 x r2 => have hh := h .xH; simp [get'] at hh
  | Node110 l x ih =>
      intro m2 h
      cases m2 with
      | Node001 r => have hh := h .xH; simp [get'] at hh
      | Node010 y =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hx := h (.xO i); simp [get'] at hx
          exfalso
          exact hi hx
      | Node011 y r =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hx := h (.xO i); simp [get'] at hx
          exfalso
          exact hi hx
      | Node100 l2 => have hh := h .xH; simp [get'] at hh
      | Node101 l2 r => have hh := h .xH; simp [get'] at hh
      | Node110 l2 y =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          have hl : l = l2 := ih l2 (by intro i; exact h (.xO i))
          cases hxy; cases hl; rfl
      | Node111 l2 y r =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          have hl : l = l2 := ih l2 (by intro i; exact h (.xO i))
          rcases tree'_not_empty r with ⟨i, hi⟩
          have hx := h (.xI i); simp [get'] at hx
          exfalso
          exact hi hx.symm
  | Node111 l x r ihl ihr =>
      intro m2 h
      cases m2 with
      | Node001 r2 => have hh := h .xH; simp [get'] at hh
      | Node010 y =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hx := h (.xO i); simp [get'] at hx
          exfalso
          exact hi hx
      | Node011 y r2 =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          rcases tree'_not_empty l with ⟨i, hi⟩
          have hx := h (.xO i); simp [get'] at hx
          exfalso
          exact hi hx
      | Node100 l2 => have hh := h .xH; simp [get'] at hh
      | Node101 l2 r2 => have hh := h .xH; simp [get'] at hh
      | Node110 l2 y =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          have hl : l = l2 := ihl l2 (by intro i; exact h (.xO i))
          rcases tree'_not_empty r with ⟨i, hi⟩
          have hx := h (.xI i); simp [get'] at hx
          exfalso
          exact hi hx
      | Node111 l2 y r2 =>
          have hh := h .xH; simp [get'] at hh
          have hxy : x = y := hh
          have hl : l = l2 := ihl l2 (by intro i; exact h (.xO i))
          have hr : r = r2 := ihr r2 (by intro i; exact h (.xI i))
          cases hxy; cases hl; cases hr; rfl

private theorem test_ext_tree_proof {A : Type} (m1 m2 : tree A) :
    (∀ i, get i m1 = get i m2) → m1 = m2 := by
  cases m1 with
  | Empty =>
      cases m2 with
      | Empty => intro h; rfl
      | Nodes m2 =>
          intro h
          rcases tree'_not_empty m2 with ⟨i, hi⟩
          have hh := h i
          simp [get] at hh
          exact False.elim (hi hh.symm)
  | Nodes m1 =>
      cases m2 with
      | Empty =>
          intro h
          rcases tree'_not_empty m1 with ⟨i, hi⟩
          have hh := h i
          simp [get] at hh
          exact False.elim (hi hh)
      | Nodes m2 =>
          intro h
          congr
          apply test_ext_tree'_proof
          intro i
          exact h i

theorem extensionality : extensionalityStatement := by
  intro A m1 m2 h
  exact test_ext_tree_proof m1 m2 h

end PTree
end CompCert4Lean.Lib.Maps

namespace CompCert4Lean.Lib.Maps.PTree

theorem prev_involutive_proof : CompCert4Lean.Lib.Maps.PTree.prev_involutiveStatement :=
  prev_involutive

end CompCert4Lean.Lib.Maps.PTree
