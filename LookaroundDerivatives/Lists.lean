open List


theorem append_singleton_iff  (w : List A) (a : A)
                             : ∃ (h : A) (t : List A), w ++ [a] = h :: t := by
  induction w with
  | nil => exists a , []
  | cons b w ih =>
      have ⟨h, t, eq⟩ := ih
      exists b, h :: t
      rw [List.cons_append, eq]



def List.productWith (f : A → B → C) (xs : List A) (ys : List B) : List C :=
  xs.flatMap λ x =>
  ys.flatMap λ y =>
  [f x y]

#eval List.productWith (· + ·) [1,2,3] ([7,8])

def subs (xs : List A) : List (List A) :=
  match xs with
  | [] => [[]]
  | x :: xs => List.flatMap (λ s => [s, x :: s]) (subs xs)

#eval subs [1,2,3]

def neSubs (xs : List A) : List (List A) :=
  List.tail (subs xs)

#eval List.length (neSubs [1,2,3,4,5,6,7,8,9,10])


def List.intersect [DecidableEq A] (xs ys : List A) : List A :=
  List.filter (λ x => List.elem x ys) xs


def splits (xs : List A) : List (List A × List A) :=
  match xs with
  | [] => ([], []) :: []
  | x :: xs => ([], x :: xs) :: List.map (λ (p, s) => (x :: p, s)) (splits xs)


theorem splits_cons {x : A}{xs : List A}
                    : splits (x :: xs)
                      = ([], x :: xs) :: List.map (λ (p, s) => (x :: p, s)) (splits xs) :=
  by rfl



theorem splits_ne (xs : List A)
                  : ∃ ps, splits xs = ([], xs) :: ps := by
  match xs with
  | [] => exists []
  | x :: xs => exists List.map (λ (p, s) => (x :: p, s)) (splits xs)


def addToHead (x : A) (xs : List (List A)) : List (List A) :=
  match xs with
  | [] => []
  | w :: xs => (x :: w) :: xs

theorem addToHead_head (a : A) {ws : List (List A)} (ne : ¬ ws = []) (ws' : List (List A))
                       : addToHead a (ws ++ ws') = addToHead a ws ++ ws' := by
  match ws with
  | [] => contradiction
  | w :: ws => simp [addToHead]

theorem addToHead_nonEmpty (x : A) {xs : List (List A)} (h : ¬ xs = [])
                           : ¬ addToHead x xs = [] := by
  match xs with
  | [] => contradiction
  | w :: xs => simp [addToHead]



def addToLast (x : A) (xs : List (List A)) : List (List A) :=
  match xs with
  | []      => []
  | [w]     => (w ++ [x]) :: []
  | w :: xs => w :: addToLast x xs

theorem addToLast_tail (a : A) (w : List A) {ws : List (List A)} (ne : ¬ ws = [])
                   : addToLast a (w :: ws) = w :: addToLast a ws := by
  match ws with
  | [] => contradiction
  | w' :: ws => simp [addToLast]


theorem foldl_addToLast {X A}
                        (f : X → List A → X)
                        (act : ∀ (xs ys : List A) (x : X), f x (xs ++ ys) = f (f x xs) ys)
                        (x : X)
                        (a : A) (w : List A) (ws : List (List A))
                        : List.foldl f x (addToLast a (w :: ws)) = f (List.foldl f x (w :: ws)) [a] := by
  match ws with
  | [] =>
      simp [addToLast, act]
  | w' :: ws =>
      simp [addToLast]
      apply foldl_addToLast f act



theorem addToHead_addToLast (a b : A) (ws : List (List A))
                            : addToHead a (addToLast b ws) = addToLast b (addToHead a ws) := by
  match ws with
  | [] => simp [addToLast, addToHead]
  | [w] => simp [addToLast, addToHead]
  | w :: w' :: ws => simp [addToLast, addToHead]



def neSplits (x : A) (xs : List A) : List (List (List A)) :=
  match xs with
  | [] => [[x]] :: []
  | y :: xs =>
      let ss := neSplits y xs
      List.flatMap (λ ws => [addToHead x ws, [x] :: ws]) ss


#eval neSplits 1 [2,3]

/-

[[2, 3]]
[[2], [3]]

[[1, 2, 3]], [[1], [2, 3]]
[[[1, 2], [3]], [[1], [2], [3]]]

-/


theorem flatMap_congr {A B} {xs ys : List A} {f g : A → List B}
                      (eq : xs = ys) (h : ∀ a, f a = g a)
                      : List.flatMap f xs = List.flatMap g ys := by
  match ys with
  | [] => simp [eq]
  | x :: xs =>
      simp [eq, h x]
      apply flatMap_congr rfl h

theorem flatMap_congr' {A B} {xs : List A} {f g : A → List B}
                       (h : ∀ x ∈ xs, f x = g x)
                       : List.flatMap f xs = List.flatMap g xs := by
  match xs with
  | [] => simp
  | x' :: xs =>
      simp
      congr 1
      . apply h
        simp
      . apply flatMap_congr'
        intro x x_in
        apply h x
        simp [x_in]



theorem neSplits_nonEmpty (x : A) (xs : List A)
          : ¬ neSplits x xs = [] := by
  match xs with
  | [] => simp [neSplits]
  | y :: xs =>
      intro eq
      rw [neSplits] at eq
      have ih := neSplits_nonEmpty y xs
      have ⟨h, t, eq'⟩ := List.ne_nil_iff_exists_cons.mp ih
      simp [eq'] at eq


theorem neSplits_elems_nonEmpty {A} (x : A) (xs : List A)
          : ∀ ws ∈ neSplits x xs, ¬ ws = [] ∧ ∀ w ∈ ws, ¬ w = [] := by
  intro ws ws_in
  match xs with
  | [] => simp [neSplits] at ws_in
          apply And.intro
          . simp [ws_in]
          . intro w w_in
            simp [ws_in] at w_in
            simp [w_in]

  | y :: xs =>

      simp [neSplits] at ws_in
      have ⟨ws', ws'_in, ws_eq⟩ := ws_in

      apply Or.elim ws_eq
      . intro ws_eq
        simp [ws_eq]
        have ⟨neq, ih⟩ := neSplits_elems_nonEmpty y xs ws' ws'_in
        apply And.intro
        . exact addToHead_nonEmpty x neq
        . intro w w_in
          have ⟨h, t, eq'⟩ := List.ne_nil_iff_exists_cons.mp neq
          simp [eq', addToHead] at w_in
          apply Or.elim w_in
          . intro eq; simp [eq]
          . intro w_in;
            have w_in' : w ∈ ws' := by simp [eq', w_in]
            exact ih w w_in'

      . intro ws_eq
        simp [ws_eq]
        intro w w_in
        have ⟨neq, ih⟩ := neSplits_elems_nonEmpty y xs ws' ws'_in
        exact ih w w_in



theorem neSplits_snoc {A} (x y : A) (xs : List A)
                      : neSplits x (xs ++ [y])
                        =
                        List.map (addToLast y) (neSplits x xs)
                        ++ List.map (λ ws => ws ++ [[y]]) (neSplits x xs) := by
  match xs with
  | [] => simp [neSplits, addToHead, addToLast]
  | x' :: xs =>
      rw [List.cons_append, neSplits]
      rw [neSplits_snoc]
      rw [List.flatMap_append]
      rw [List.flatMap_map]
      rw [List.flatMap_map]

      rw [neSplits]
      rw [List.map_flatMap]
      rw [List.map_flatMap]

      simp
      congr 1

      . apply flatMap_congr'
        intro ws ws_in
        simp
        apply And.intro
        . rw [addToHead_addToLast]
        . have ⟨ne, _⟩ := neSplits_elems_nonEmpty x' xs ws ws_in
          rw [addToLast_tail]
          exact ne

      . apply flatMap_congr'
        intro ws ws_in
        simp
        have ⟨ne, _⟩ := neSplits_elems_nonEmpty x' xs ws ws_in
        rw [addToHead_head]
        exact ne


---------------------------------------------------

theorem productWith_mem {A B C} {xs : List A}{ys : List B}{f : A → B → C} {z : C}
                        : z ∈ List.productWith f xs ys
                          ↔
                          ∃ x y, z = f x y ∧ x ∈ xs ∧ y ∈ ys := by
  rw [List.productWith]
  simp
  constructor
  . intro ⟨x, x_in, y, y_in, eq⟩
    exists x, y
  . intro ⟨x, y, eq, x_in, y_in⟩
    exists x
    apply And.intro x_in
    exists y



theorem subs_eq_cons {A} (xs : List A) : ∃ t, subs xs = [] :: t := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      have ⟨t', ht'⟩ := ih
      simp [subs]
      simp [ht']

theorem mem_singleton_subs {A} {x : A} {xs : List A} : [x] ∈ subs xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [subs]
  | cons y ys ih =>
    simp [subs]
    constructor
    · intro ⟨s, hs, hmem⟩
      rcases hmem with h | ⟨h₁, h₂⟩
      · simp [ih.mp, h, hs]
      · subst h₁ h₂
        simp
    · intro h
      rcases h with h | h
      · simp [h]
        have ⟨t, ht⟩ := subs_eq_cons ys
        exact ⟨[], by simp [ht]⟩
      · exact ⟨[x], by simp [ih.mpr h]⟩

theorem singleton_neSubs {A} {x : A}{xs : List A} : [x] ∈ neSubs xs ↔ x ∈ xs  := by
  have ⟨t, ht⟩ := subs_eq_cons xs
  simp [neSubs, ht]
  rw [←mem_singleton_subs (x := x)]
  rw [ht]
  simp

theorem subs_eq_neSubs {A} (xs : List A) : subs xs = [] :: neSubs xs := by
  have ⟨t, ht⟩ := subs_eq_cons xs
  rw [neSubs, ht]
  simp


theorem subs_complete {A} {s xs : List A} (h : s <+ xs) : s ∈ subs xs := by
  induction h with
  | slnil => simp [subs]
  | @cons ys' zs' x _ ih =>
      simp [subs]
      exists ys'
      simp [ih]
  | @cons₂ ys' zs' x _ ih =>
      simp [subs]
      exists ys'
      simp [ih]

theorem neSubs_complete {A} {s xs : List A}
               (ne : s ≠ []) (sl : s <+ xs)
               : s ∈ neSubs xs := by
  have hs : s ∈ subs xs := subs_complete sl
  rw [subs_eq_neSubs xs] at hs
  rcases List.mem_cons.mp hs with eq | mem
  · contradiction
  · exact mem


theorem mem_productWith_of {A} {es fs : List A} {ps : List (A × A)}
                           (g : A → A → A)
                           (sub : ∀ p ∈ ps, p.1 ∈ es ∧ p.2 ∈ fs)
                           : ∀ m ∈ List.map (Function.uncurry g) ps,
                               m ∈ List.productWith g es fs := by
  intro a a_in
  have ⟨⟨e', f'⟩, ef_in, eq⟩ := List.mem_map.mp a_in
  have ⟨e'_in, f'_in⟩ := sub (e', f') ef_in
  apply productWith_mem.mpr
  exists e', f'
  exact ⟨eq.symm, e'_in, f'_in⟩



def sublistOfElems {A} [DecidableEq A] (ms xs : List A) : List A :=
  List.filter (List.contains ms) xs

theorem sublistOfElems_is_sublist {A} [DecidableEq A] {xs ms : List A}
                                  : sublistOfElems ms xs <+ xs := by
  rw [sublistOfElems]
  exact filter_sublist

theorem sublistOfElems_complete {A} [DecidableEq A] {xs ms : List A}
                                (sub : ms ⊆ xs)
                                : ∀ y, y ∈ ms ↔ y ∈ sublistOfElems ms xs := by
  rw [sublistOfElems]
  match xs with
  | [] => simp at sub
          simp [sub]

  | x :: xs =>
      simp only [mem_filter, contains_eq_mem, decide_eq_true_iff]
      intro y
      constructor
      . intro y_ms
        exact ⟨sub y_ms, y_ms⟩
      . intro ⟨p, y_ms⟩
        exact y_ms

theorem sublistOfElems_ne {A} [DecidableEq A] {xs ms : List A}
                          (sub : ms ⊆ xs)
                          (ne : ms ≠ [])
                          : sublistOfElems ms xs ≠ [] := by
  intro eq
  have ⟨b, l', eq'⟩ := ne_nil_iff_exists_cons.mp ne
  have cmpl := sublistOfElems_complete sub b
  rw [eq, eq'] at cmpl
  simp at cmpl



theorem exists_sublist_same {A} [DecidableEq A] {ms xs : List A}
                            (sub : ms ⊆ xs)
                            : ∃ xs' : List A,
                                (ms ≠ [] → xs' ≠ []) ∧
                                xs' <+ xs ∧
                                ∀ x, x ∈ ms ↔ x ∈ xs' := by
  exists sublistOfElems ms xs
  exact ⟨λ ne => sublistOfElems_ne sub ne,
         sublistOfElems_is_sublist,
         sublistOfElems_complete sub⟩


-------------------------------------------------------------------

def focus {A} (xs : List A) : List (List A × A × List A) :=
  match xs with
  | [] => []
  | x :: xs => ([], x, xs) ::
               List.map (λ (l, c, r) => (x :: l, c, r))
                        (focus xs)

#eval focus [1,2,3,4]


theorem focus_append {A} (xs ys : List A)
                     : focus (xs ++ ys)
                       =
                       List.map (λ (l, c, r) => (l, c, r ++ ys)) (focus xs)
                       ++
                       List.map (λ (l, c, r) => (xs ++ l, c, r)) (focus ys) := by
  match xs with
  | [] => rw [nil_append, focus, map_nil, nil_append]
          rw [map_id'']
          simp

  | x :: xs =>
      rw [cons_append, focus]
      rw [focus_append]
      rw [map_append, map_map, map_map]

      rw [focus, map_cons]

      apply cons_eq_cons.mpr
      apply And.intro
      . rfl

      . rw [append_eq]
        apply append_eq_append_iff.mpr
        left
        exists []
        simp
