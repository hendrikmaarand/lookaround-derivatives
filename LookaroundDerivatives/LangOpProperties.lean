import LookaroundDerivatives.Language


theorem leq_refl : ∀ {l : Lang α}, l ≐ l := by
  intro l t
  rfl

theorem leq_symm : ∀ {k l : Lang α}, k ≐ l → l ≐ k := by
  intro k l eq t
  rw [eq t]

theorem leq_trans : ∀ {l₁ l₂ l₃ : Lang α}, l₁ ≐ l₂ → l₂ ≐ l₃ → l₁ ≐ l₃ := by
  intro l₁ l₂ l₃ eq eq' t
  rw [eq t, eq' t]


------------------------------------------------------
-- congruences of constructors

theorem union_congr {k k' l l' : Lang α} : k ≐ k' → l ≐ l' → k ∪ l ≐ k' ∪ l' := by
  intro k_eq l_eq t
  rw [union, union]
  rw [k_eq, l_eq]

theorem concat_congr {k k' l l' : Lang α} : k ≐ k' → l ≐ l' → k ⊙ l ≐ k' ⊙ l' := by
  intro k_eq l_eq t
  rw [concat, concat]
  apply Iff.intro
  . intro ⟨m₁, m₂, mt_eq, k_m, l_m⟩
    exists m₁, m₂
    simp [mt_eq, ←k_eq (behind t, m₁, m₂ ++ ahead t), ←l_eq (behind t ++ m₁, m₂, ahead t)]
    exact ⟨k_m, l_m⟩

  . intro ⟨m₁, m₂, mt_eq, k_m, l_m⟩
    exists m₁, m₂
    simp [mt_eq, k_eq (behind t, m₁, m₂ ++ ahead t), l_eq (behind t ++ m₁, m₂, ahead t)]
    exact ⟨k_m, l_m⟩

theorem intersection_congr {k k' l l' : Lang α} : k ≐ k' → l ≐ l' → k ∩ l ≐ k' ∩ l' := by
  intro k_eq l_eq t
  rw [intersection, intersection]
  rw [k_eq, l_eq]

theorem diff_congr {k k' l l' : Lang α} : k ≐ k' → l ≐ l' → k \ l ≐ k' \ l' := by
  intro k_eq l_eq t
  rw [diff, diff]
  rw [k_eq, l_eq]


theorem kstar_congr' {α} {l l' : Lang α} (l_eq : l ≐ l') (t : Triple α)
                     : StarLFP l t ↔ StarLFP l' t := by
  apply Iff.intro
  . intro kl_mem
    induction kl_mem with
    | base h => exact .base h
    | @step lb m₁ m₂ la m eq l_mem ls_mem ih =>
        apply StarLFP.step eq
        . rw [←l_eq]
          exact l_mem
        . exact ih

  . intro kl_mem
    induction kl_mem with
    | base h => exact .base h
    | @step lb m₁ m₂ la m eq l_mem ls_mem ih =>
        apply StarLFP.step eq
        . rw [l_eq]
          exact l_mem
        . exact ih

theorem kstar_congr {l l' : Lang α} : l ≐ l' → l⋆ ≐ l'⋆ := by
  intro eq t
  rw [kstar, kstar]
  exact kstar_congr' eq t



theorem lookbehind_congr {l l' : Lang α} : l ≐ l' → ◁ l ≐ ◁ l' := by
  intro l_eq t
  rw [lookbehind, lookbehind]
  rw [l_eq]

theorem lookahead_congr {l l' : Lang α} : l ≐ l' → ▷ l ≐ ▷ l' := by
  intro l_eq t
  rw [lookahead, lookahead]
  rw [l_eq]


-------------------------------------------------------------------------

theorem union_assoc : ∀ {l₁ l₂ l₃ : Lang α}, l₁ ∪ (l₂ ∪ l₃) ≐ (l₁ ∪ l₂) ∪ l₃ := by
  intro l₁ l₂ l₃ t
  simp [union, or_assoc]

theorem union_comm : ∀ {k l : Lang α}, k ∪ l ≐ l ∪ k := by
  intro k l t
  simp [union, or_comm]

theorem union_idem : ∀ {l : Lang α}, l ∪ l ≐ l := by
  intro l t
  simp [union]


theorem union_identity_l : ∀ {l : Lang α}, ∅ ∪ l ≐ l := by
  intro l t
  simp [union, empty]

theorem union_identity_r : ∀ {l : Lang α}, l ∪ ∅ ≐ l := by
  intro l t
  rw [union_comm, union_identity_l]

-----------------------------------------------------------------------

theorem concat_assoc : ∀ {k l m : Lang α}, k ⊙ (l ⊙ m) ≐ (k ⊙ l) ⊙ m := by
  intro k l m t
  apply Iff.intro
  . intro ⟨x, y, mt_eq, k_m, lm_m⟩
    have ⟨z, w, mt_eq', l_m, m_m⟩ := lm_m
    rw [behind, mtch, ahead] at *
    subst mt_eq'
    exists (x ++ z), w
    simp at k_m l_m m_m
    simp [mt_eq, m_m]
    exists x, z

  . intro ⟨xy, z, mt_eq, kl_m, m_m⟩
    have ⟨x, y, mt_eq', k_m, l_m⟩ := kl_m
    rw [behind, mtch, ahead] at *
    subst mt_eq'
    exists x, y ++ z
    simp [mt_eq, k_m]
    exists y, z
    rw [behind, mtch, ahead] at *
    simp
    exact ⟨l_m, m_m⟩


theorem concat_zero_l : ∀ {l : Lang α}, ∅ ⊙ l ≐ ∅ := by
  intro l t
  simp [concat, empty]

theorem concat_zero_r : ∀ {l : Lang α}, l ⊙ ∅ ≐ ∅ := by
  intro l t
  simp [concat, empty]

theorem concat_unit_l : ∀ {l : Lang α}, 𝟙 ⊙ l ≐ l := by
  intro l t
  simp [concat, unit]
  apply Iff.intro
  . intro ⟨m₁, m₂, eq₁, eq₂, mem⟩
    rw [mtch] at eq₂
    subst eq₂
    simp_all
    rw [←eq₁] at mem
    exact mem

  . intro mem
    exists [], mtch t
    rw [mtch]
    simp
    exact mem

theorem concat_unit_r : ∀ {l : Lang α}, l ⊙ 𝟙 ≐ l := by
  intro l t
  simp [concat, unit]
  apply Iff.intro
  . intro ⟨m₁, m₂, eq₁, mem, eq₂⟩
    rw [mtch] at eq₂
    subst eq₂
    simp_all
    rw [←eq₁] at mem
    exact mem
  . intro mem
    exists mtch t, []
    rw [mtch]
    simp
    exact mem

theorem concat_unit_l_der : ∀ {a : α} {l : Lang α}, ◁ 𝟙 ⊙ (der a l) ≐ der a l := by
  intro a l t
  simp [concat, lookbehind, unit]
  apply Iff.intro
  . intro ⟨m₁, m₂, eq₁, ⟨eq₂, eq₃⟩, mem⟩
    rw [mtch] at eq₂
    rw [mtch, behind] at eq₃
    subst eq₂
    simp_all
    rw [←eq₁] at mem
    rw [triple_eta t]
    rw [eq₃]
    exact mem

  . intro mem
    exists [], mtch t
    rw [mtch, mtch, behind]
    simp
    exact ⟨der_mem' mem, mem⟩

theorem concat_unit_l_derLAhd : ∀ {a : α} {l : Lang α}, ◁ 𝟙 ⊙ (derLAhd a l) ≐ derLAhd a l := by
  intro a l t
  simp [concat, lookbehind, unit]
  apply Iff.intro
  . intro ⟨m₁, m₂, eq₁, ⟨eq₂, eq₃⟩, mem⟩
    rw [mtch] at eq₂
    rw [mtch, behind] at eq₃
    subst eq₂
    simp_all
    rw [←eq₁] at mem
    rw [triple_eta t]
    rw [eq₃]
    exact mem

  . intro mem
    exists [], mtch t
    rw [mtch, mtch, behind]
    simp
    exact ⟨(derLAhd_mem' mem).1, mem⟩

-------------------------------------------------------------------------

theorem inter_assoc : ∀ {l₁ l₂ l₃ : Lang α}, l₁ ∩ (l₂ ∩ l₃) ≐ (l₁ ∩ l₂) ∩ l₃ := by
  intro l₁ l₂ l₃ t
  simp [intersection, and_assoc]

theorem inter_comm : ∀ {k l : Lang α}, k ∩ l ≐ l ∩ k := by
  intro k l t
  simp [intersection, and_comm]

theorem inter_idem : ∀ {l : Lang α}, l ≐ l ∩ l := by
  intro l t
  simp [intersection]


theorem inter_zero_l : ∀ {l : Lang α}, ∅ ∩ l ≐ ∅ := by
  intro l t
  simp [intersection, empty]

theorem inter_zero_r : ∀ {l : Lang α}, l ∩ ∅ ≐ ∅ := by
  intro l t
  rw [inter_comm, inter_zero_l]

theorem inter_top_l : ∀ {l : Lang α}, 𝕋 ∩ l ≐ l := by
  intro l t
  simp [intersection, top]

theorem inter_top_r : ∀ {l : Lang α}, l ∩ 𝕋 ≐ l := by
  intro l t
  rw [inter_comm, inter_top_l]


theorem union_over_inter : ∀ {k l m : Lang α},
                                 k ∪ (l ∩ m) ≐ (k ∪ l) ∩ (k ∪ m) := by
  intro k l m t
  rw [union, intersection, intersection, union, union]
  rw [or_and_left]

theorem inter_over_union : ∀ {k l m : Lang α},
                                 k ∩ (l ∪ m) ≐ (k ∩ l) ∪ (k ∩ m) := by
  intro k l m t
  rw [union, intersection, intersection, union, intersection]
  rw [and_or_left]


theorem union_absorb : ∀ {k l : Lang α},
                         k ∪ (k ∩ l) ≐ k := by
  intro k l t
  rw [union, intersection]
  calc k t ∨ k t ∧ l t
    _ ↔ k t ∧ True ∨ k t ∧ l t := by rw [and_true]
    _ ↔ k t ∧ (True ∨ l t) := by rw [and_or_left]
    _ ↔ k t := by simp

theorem inter_absorb : ∀ {k l : Lang α},
                         k ∩ (k ∪ l) ≐ k := by
  intro k l t
  rw [intersection, union]
  calc k t ∧ (k t ∨ l t)
    _ ↔ (k t ∨ False) ∧ (k t ∨ l t)  := by rw [or_false]
    _ ↔ k t ∨  (False ∧ l t)  := by rw[or_and_left]
    _ ↔ k t := by simp


---------------------------------------------------------------------------

theorem diff_zero_l : ∀ {l : Lang α}, ∅ \ l ≐ ∅ := by
  intro l t
  simp [diff, empty]

theorem diff_top_r : ∀ {l : Lang α}, l \ 𝕋 ≐ ∅ := by
  intro l t
  simp [diff, top, empty]

theorem union_compl : ∀ {l : Lang α}, l ∪ (𝕋 \ l) ≐ 𝕋 := by
  intro l t
  simp [union, diff, top]
  open Classical in
  apply em

theorem inter_compl : ∀ {l : Lang α}, l ∩ (𝕋 \ l) ≐ ∅ := by
  intro l t
  rw [intersection, empty, diff, top]
  simp



-----------------------------------------------------------------------------

theorem lbhd_unit_lahd {α} : @LEq α (◁ 𝟙) (▷ (◁ 𝟙 ⊙ 𝕋)) := by
  intro t
  rw [lookbehind, unit, mtch, lookahead]
  apply Iff.intro
  . intro ⟨mt_eq, bt_eq⟩
    simp [mt_eq]
    exists [], ahead t

  . intro ⟨mt_eq, mem⟩
    rw [concat, mtch, behind, ahead] at mem
    have ⟨m₁, m₂, at_eq, m, _⟩ := mem
    rw [lookbehind, unit, mtch, mtch, behind] at m
    exact ⟨mt_eq, m.2⟩


theorem lbhd_zero {α} : @LEq α (◁ ∅) ∅ := by
  intro t
  simp [lookbehind, empty]

-------------------------------------------------------------------------------

theorem lahd_zero {α} : @LEq α (▷ ∅) ∅ := by
  intro t
  simp [lookahead, empty]

theorem lahd_unit_lbhd : @LEq α (▷ 𝟙) (◁ (𝕋 ⊙ ▷ 𝟙)) := by
  intro t
  rw [lookahead, unit, mtch, lookbehind]
  apply Iff.intro
  . intro ⟨mt_eq, at_eq⟩
    simp [mt_eq, at_eq]
    exists behind t, []
    simp [top, lookahead, unit, mtch, ahead]

  . intro ⟨mt_eq, mem⟩
    rw [concat, mtch, behind, ahead] at mem
    have ⟨m₁, m₂, at_eq, _, m⟩ := mem
    rw [lookahead, unit, mtch, mtch, ahead] at m
    exact ⟨mt_eq, m.2⟩


theorem lahd_inter : ∀ {k l : Lang α}, ▷ k ∩ ▷ l ≐ ▷ (k ∩ l) := by
  intro k l t
  simp [lookahead, intersection]
  ac_nf

theorem lahd_union : ∀ {k l : Lang α}, ▷ k ∪ ▷ l ≐ ▷ (k ∪ l) := by
  intro k l t
  simp [lookahead, union, and_or_left]

theorem lahd_diff : ∀ {k l : Lang α}, ▷ k \ ▷ l ≐ ▷ (k \ l) := by
  intro k l t
  simp [lookahead, diff]
  grind


theorem lahd_concat_assoc : ∀ {l₁ l₂ l₃ : Lang α},
                                ▷ l₁ ⊙ (▷ l₂ ⊙ l₃) ≐ (▷ l₁ ⊙ ▷ l₂) ⊙ l₃ := by
  intro l₁ l₂ l₃ t
  rw [concat_assoc]

theorem lahd_concat_inter {α} : ∀ {k l : Lang α}, ▷ k ⊙ ▷ l ≐ ▷ k ∩ ▷ l := by
  intro k l t
  apply Iff.intro
  . intro ⟨m₁, m₂, eq, lk_mem, ll_mem⟩
    rw [lookahead] at lk_mem ll_mem
    rw [mtch, behind, ahead] at lk_mem ll_mem
    rw [lk_mem.1] at ll_mem eq
    rw [ll_mem.1] at lk_mem eq
    rw [intersection, lookahead, lookahead]
    simp [eq]
    simp at lk_mem ll_mem
    exact ⟨lk_mem.2, ll_mem.2⟩

  . intro ⟨lk_mem, ll_mem⟩
    rw [concat]
    rw [lookahead] at lk_mem ll_mem

    exists [], []
    rw [lookahead, lookahead, mtch, behind, ahead, mtch, behind, ahead]

    simp [lk_mem, ll_mem]


--------------------------------------------------------------------------

theorem concat_distr_union_l : ∀ {k l₁ l₂ : Lang α}, k ⊙ (l₁ ∪ l₂) ≐ (k ⊙ l₁) ∪ (k ⊙ l₂) := by
  intro k l₁ l₂ t
  apply Iff.intro
  . intro ⟨m₁, m₂, eq, k_mem, l_mem⟩
    rw [union] at l_mem
    rw [union]
    apply Or.elim l_mem
    . intro l₁_mem
      apply Or.inl
      exists m₁, m₂
    . intro l₂_mem
      apply Or.inr
      exists m₁, m₂

  . intro mem
    apply Or.elim mem
    . intro ⟨m₁, m₂, eq, k_mem, l₁_mem⟩
      exists m₁, m₂
      rw [union]
      simp [eq, k_mem, l₁_mem]

    . intro ⟨m₁, m₂, eq, k_mem, l₂_mem⟩
      exists m₁, m₂
      rw [union]
      simp [eq, k_mem, l₂_mem]


theorem concat_distr_union_r : ∀ {k l m : Lang α}, (k ∪ l) ⊙ m ≐ (k ⊙ m) ∪ (l ⊙ m) := by
  intro k l m t
  apply Iff.intro
  . intro ⟨x, y, mt_eq, kl_m, m_m⟩
    rw [union] at *
    rcases kl_m with k_m | l_m
    . left
      exists x, y
    . right
      exists x, y

  . intro p
    rcases p with ⟨x, y, mt_eq, k_m, m_m⟩ | ⟨x, y, mt_eq, l_m, m_m⟩
    . exists x, y
      simp [mt_eq, m_m]
      exact Or.inl k_m
    . exists x, y
      simp [mt_eq, m_m]
      exact Or.inr l_m

-------------------------------------------------------------------------------


def iterR (n : Nat) (l : Lang α) : Lang α :=
  match n with
  | .zero => 𝟙
  | .succ n => l ⊙ iterR n l

theorem kstar_iterR {α} {l : Lang α} {t : Triple α} (ls_m : l⋆ t) : ∃ n, iterR n l t := by
  induction ls_m with
  | base u_m => exists 0
  | @step lb m₁ m₂ la m eq l_m' ls_m' ih =>
      have ⟨n, i_m⟩ := ih
      exists n + 1
      exists m₁, m₂

theorem iterR_kstar {α} {l : Lang α} {t : Triple α} {n : Nat} (i_m : iterR n l t) : l⋆ t := by
  match n with
  | .zero => exact StarLFP.base i_m
  | .succ n =>
      rw [iterR] at i_m
      have ⟨y₁, y₂, eq, l_m, i_m'⟩ := i_m
      have ls_m := iterR_kstar i_m'
      exact StarLFP.step eq l_m ls_m

-- Kleene star of l is iterated multiplication of l.
theorem kstar_iter_equiv {α} (l : Lang α) {t : Triple α} : l⋆ t ↔ ∃ n, iterR n l t :=
  Iff.intro kstar_iterR
            (λ ⟨_, i_m⟩ => iterR_kstar i_m)


theorem iterR_succ {α} (n : Nat) (l : Lang α) : iterR n l ⊙ l ≐ iterR (n + 1) l := by
  intro t
  match n with
  | .zero =>
      rw [iterR, iterR, iterR]
      rw [concat_unit_l, concat_unit_r]

  | .succ n =>
      rw [iterR, iterR]
      rw [←concat_assoc]
      apply Iff.intro
      . intro ⟨y₁, y₂, eq, l_m, mem⟩
        rw [iterR_succ n l] at mem
        exists y₁, y₂
      . intro ⟨y₁, y₂, eq, l_m, i_m⟩
        rw [←iterR_succ n l] at i_m
        exists y₁, y₂


theorem iterR_succ' {α} (n : Nat) (l : Lang α) : iterR (n + 1) l ≐ l ⊙ iterR n l := by
  intro t
  rw [iterR]



theorem kstar_concat_lem : ∀ {l : Lang α}, l ⊙ l⋆ ≐ l⋆ ⊙ l := by
  intro l t
  apply Iff.intro
  . intro ⟨y₁, y₂, eq, l_m, ls_m⟩
    have ⟨n, i_m⟩ := (kstar_iter_equiv l).mp ls_m
    have mem : (l ⊙ iterR n l) t := ⟨y₁, y₂, eq, l_m, i_m⟩
    rw [←iterR_succ'] at mem
    rw [←iterR_succ] at mem
    have ⟨y₁, y₂, eq, i_m, l_m⟩ := mem
    have ls_m := iterR_kstar i_m
    exists y₁, y₂
  . intro ⟨y₁, y₂, eq, ls_m, l_m⟩
    have ⟨n, i_m⟩ := (kstar_iter_equiv l).mp ls_m
    have mem : (iterR n l ⊙ l) t := ⟨y₁, y₂, eq, i_m, l_m⟩
    rw [iterR_succ] at mem
    rw [iterR_succ'] at mem
    have ⟨y₁, y₂, eq, l_m, i_m⟩ := mem
    have ls_m := iterR_kstar i_m
    exists y₁, y₂



theorem kstar_expand : ∀ {l : Lang α}, l⋆ ≐ 𝟙 ∪ l ⊙ l⋆ := by
  intro l t
  rw [kstar, union]
  apply Iff.intro
  . intro kl_mem
    match kl_mem with
    | .base h => simp [h]
    | .step (m₁ := m₁) (m₂ := m₂) p q r =>
        rw [concat]
        apply Or.inr
        exists m₁, m₂

  . intro p
    apply Or.elim p
    . intro h
      exact .base h
    . intro ⟨m₁, m₂, eq, l_mem, k_mem⟩
      exact .step eq l_mem k_mem

theorem kstar_expand' : ∀ {l : Lang α}, l⋆ ≐ 𝟙 ∪ l⋆ ⊙ l := by
  intro l t
  rw [kstar_expand]
  rw [union]
  rw [kstar_concat_lem]
  rw [←union]


def LEqSubset (k l : Lang α) := ∀ {t}, k t → l t

infix:50 " ⊆ " => LEqSubset

theorem subset_union_lemma {k l : Lang α} : k ⊆ l ↔ k ∪ l ≐ l := by
  apply Iff.intro
  . intro ss
    intro t
    rw [union]
    simp
    exact ss

  . intro leq
    intro t k_t
    rw [←leq, union]
    simp [k_t]



theorem iterR_lfp : ∀ {a b x : Lang α} {n : Nat},
                          b ∪ a ⊙ x ⊆ x → iterR n a ⊙ b ⊆ x := by
  intro a b x n
  intro ss t mem
  match n with
  | .zero =>
      rw [iterR, concat_unit_l] at mem
      apply @ss t
      rw [union]
      left
      exact mem

  | .succ n =>
      rw [iterR, ←concat_assoc] at mem
      have ih := @iterR_lfp α a b x n ss
      apply @ss t
      rw [union]
      right
      have ⟨y₁, y₂, eq, a_m, ib_m⟩ := mem
      exists y₁, y₂
      simp [eq, a_m]
      exact ih ib_m

theorem iterR_lfp' : ∀ {a b x : Lang α} {n : Nat},
                           b ∪ x ⊙ a ⊆ x → b ⊙ iterR n a ⊆ x := by
  intro a b x n
  intro ss t mem
  match n with
  | .zero =>
      rw [iterR, concat_unit_r] at mem
      apply @ss t
      rw [union]
      left
      exact mem

  | .succ n =>
      have ⟨y₁, y₂, eq, b_m, c_m⟩ := mem
      rw [←iterR_succ] at c_m
      have ih := @iterR_lfp' α a b x n ss
      apply @ss t
      rw [union]
      right
      have ⟨w₁, w₂, eq', i_m, a_m⟩ := c_m
      exists y₁ ++ w₁, w₂
      rw [behind, mtch, ahead] at *
      simp at a_m
      simp [eq, eq', a_m]
      apply ih
      exists y₁, w₁
      rw [behind, mtch, ahead]
      rw [eq', List.append_assoc] at b_m
      simp [b_m, i_m]


theorem kstar_lfp : ∀ {a b x : Lang α}, b ∪ a ⊙ x ⊆ x → a⋆ ⊙ b ⊆ x := by
  intro a b x ss
  intro t
  intro ⟨y₁, y₂, eq, as_m, b_m⟩

  have ⟨n, i_m⟩ := kstar_iterR as_m
  apply @iterR_lfp α a b x n ss

  exists y₁, y₂


theorem kstar_lfp' : ∀ {a b x : Lang α}, b ∪ x ⊙ a ⊆ x → b ⊙ a⋆ ⊆ x := by
  intro a b x ss
  intro t
  intro ⟨y₁, y₂, eq, b_m, as_m⟩

  have ⟨n, i_m⟩ := kstar_iterR as_m
  apply @iterR_lfp' α a b x n ss

  exists y₁, y₂


-------------------------------------------------------------------------------

theorem pla_from_lookahead : ∀ (l : Lang α), ▷ (l ⊙ 𝕋) ≐ pla l := by
  intro l t
  rw [lookahead, pla]
  apply Iff.intro
  . intro ⟨mt_eq, y, z, at_eq, l_m, _⟩
    rw [behind, mtch, ahead] at *
    simp at l_m
    apply And.intro mt_eq
    exists y, z

  . intro ⟨mt_eq, y, z, at_eq, l_m⟩
    apply And.intro mt_eq
    exists y, z
    rw [behind, mtch, ahead, top]
    simp [at_eq, l_m]


theorem slb_from_lookbehind : ∀ (l : Lang α), ◁ (𝕋 ⊙ l) ≐ slb l := by
  intro l t
  rw [lookbehind, slb]
  apply Iff.intro
  . intro ⟨mt_eq, x, y, bt_eq, _, l_m⟩
    rw [behind, mtch, ahead] at *
    apply And.intro mt_eq
    exists x, y

  . intro ⟨mt_eq, x, y, bt_eq, l_m⟩
    apply And.intro mt_eq
    exists x, y
