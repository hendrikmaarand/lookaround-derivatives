import LookaroundDerivatives.Triple
import LookaroundDerivatives.Language
import LookaroundDerivatives.LangOpProperties
import LookaroundDerivatives.LangDerProperties
import LookaroundDerivatives.Expressions


def sem (r : RE α) : Lang α :=
  match r with
  | .symbol b     => $ b
  | .zero         => ∅
  | .plus r s     => sem r ∪ sem s
  | .one          => 𝟙
  | .mult r s     => sem r ⊙ sem s
  | .inter r s    => sem r ∩ sem s
  | .etop         => 𝕋
  | .sub r s      => sem r \ sem s
  | .star r       => kstar (sem r)
  | .lookbehind r => ◁ (sem r)
  | .lookahead r  => ▷ (sem r)

notation "⟦" r "⟧" => sem r


theorem equiv_sound {r s : RE α} (eq : r ≡ s) : ⟦ r ⟧ ≐ ⟦ s ⟧ := by
  match eq with
  | .plusIdem  => simp [sem]
                  exact leq_symm union_idem

  | .plusComm  => simp [sem, union_comm]
  | .plusAssoc => simp [sem, union_assoc]

  | .plusZeroL => simp [sem, union_identity_l]

  | .multZeroL => simp [sem, concat_zero_l]
  | .multZeroR => simp [sem, concat_zero_r]

  | .interIdem => simp [sem, inter_idem]
  | .interComm => simp [sem, inter_comm]

  | .subZeroL => simp [sem, diff_zero_l]

  | .lbhdZero => simp [sem, lbhd_zero]
  | .lbhdUnit => simp [sem, lbhd_unit_lahd]

  | .lahdZero => simp [sem, lahd_zero]
  | .lahdInter => simp [sem, lahd_inter]
  | .lahdPlus => simp [sem, lahd_union]
  | .lahdSub => simp [sem, lahd_diff]

  | .lahdMultAssoc => simp [sem, lahd_concat_assoc]

  | @Equiv.lahdMultInter _ r1 r2 => simp [sem, lahd_concat_inter]

  | .distrL => simp [sem, concat_distr_union_l]

  | .refl eq => rw [eq]; exact leq_refl
  | .sym  eq => exact leq_symm (equiv_sound eq)
  | .trans eq₁ eq₂ => exact leq_trans (equiv_sound eq₁) (equiv_sound eq₂)

  | .plusCong r_eq s_eq => simp [sem, union_congr (equiv_sound r_eq) (equiv_sound s_eq)]
  | .multCong r_eq s_eq => simp [sem, concat_congr (equiv_sound r_eq) (equiv_sound s_eq)]
  | .interCong r_eq s_eq => simp [sem, intersection_congr (equiv_sound r_eq) (equiv_sound s_eq)]
  | .subCong r_eq s_eq => simp [sem, diff_congr (equiv_sound r_eq) (equiv_sound s_eq)]
  | .starCong r_eq => simp [sem, kstar_congr (equiv_sound r_eq)]
  | .lbhdCong r_eq => simp [sem, lookbehind_congr (equiv_sound r_eq)]
  | .lahdCong r_eq => simp [sem, lookahead_congr (equiv_sound r_eq)]




theorem N_correct (r : RE α) : nlbl ⟦ r ⟧ ↔ N r := by
  match r with
  | .symbol b =>
      rw [nlbl, sem, symb, mtch, N]
      simp
  | .zero =>
      rw [nlbl, sem, empty, N]
      simp
  | .plus r s =>
      rw [sem, nlbl_union, N, Bool.or_eq_true]
      rw [N_correct r, N_correct s]
  | .one =>
      rw [sem, nlbl, unit, mtch, N]
      simp
  | .mult r s =>
      rw [sem, nlbl_concat, N, Bool.and_eq_true]
      rw [N_correct r, N_correct s]
  | .etop =>
      rw [sem, nlbl, top, N]
      simp
  | .inter r s =>
      rw [sem, nlbl_inter, N, Bool.and_eq_true]
      rw [N_correct r, N_correct s]
  | .sub r s =>
      rw [sem, nlbl_diff, N, Bool.and_eq_true]
      rw [N_correct r, N_correct s]
      simp
  | .star r =>
      rw [sem, nlbl_kstar, N]
      simp
  | .lookbehind r =>
      rw [sem, nlbl_lookbehind, N]
      rw [N_correct r]
  | .lookahead r =>
      rw [sem, nlbl_lookahead, N]
      rw [N_correct r]



mutual

theorem DBhd_correct {α} [DecidableEq α] (a : α) (r : RE α)
    : derLBhd a ⟦ r ⟧ ≐ ⟦ DBhd a r ⟧ := by
  intro t
  match r with
  | .symbol b =>
      rw [sem, derLBhd_symb, DBhd, sem]
  | .zero =>
      rw [sem, derLBhd_empty, DBhd, sem]
  | .plus r s =>
      rw [sem, derLBhd_union, DBhd, sem]
      have ih_r := DBhd_correct a r
      have ih_s := DBhd_correct a s
      rw [union_congr ih_r ih_s]
  | .one =>
      rw [sem, derLBhd_unit, DBhd, sem]
  | .mult r s =>
      rw [sem, derLBhd_concat, DBhd, sem]
      have ih_r := DBhd_correct a r
      have ih_s := DBhd_correct a s
      rw [concat_congr ih_r ih_s]
  | .etop =>
      rw [sem, derLBhd_top, DBhd, sem]
  | .inter r s =>
      rw [sem, derLBhd_inter, DBhd, sem]
      have ih_r := DBhd_correct a r
      have ih_s := DBhd_correct a s
      rw [intersection_congr ih_r ih_s]
  | .sub r s =>
      rw [sem, derLBhd_diff, DBhd, sem]
      have ih_r := DBhd_correct a r
      have ih_s := DBhd_correct a s
      rw [diff_congr ih_r ih_s]
  | .star r =>
      rw [sem, derLBhd_kstar, DBhd, sem]
      have ih_r := DBhd_correct a r
      rw [kstar_congr ih_r]
  | .lookbehind r =>
      rw [sem, derLBhd_lookbehind, DBhd, sem]
      have ih_r := D_correct a r
      rw [lookbehind_congr ih_r]
  | .lookahead r =>
      rw [sem, derLBhd_lookahead, DBhd, sem]
      have ih_r := DBhd_correct a r
      rw [lookahead_congr ih_r]


theorem D_correct {α} [DecidableEq α] (a : α) (r : RE α)
    : der a ⟦ r ⟧ ≐ ⟦ D a r ⟧ := by
  intro t
  match r with
  | .symbol b =>
      if h : a = b then
        rw [sem, der_symb, D]
        simp [h, sem]
      else
        rw [sem, der_symb, D]
        simp [h, sem]
  | .zero =>
      rw [sem, der_empty, D, sem]
  | .plus r s =>
      rw [sem, der_union, D, sem]
      have ih_r := D_correct a r
      have ih_s := D_correct a s
      rw [union_congr ih_r ih_s]
  | .one =>
      rw [sem, der_unit, D, sem]
  | .mult r s =>
      rw [sem, der_concat, D, sem, sem, sem]

      have ih_r := D_correct a r
      have ih_s := D_correct a s
      have ih_r' := DAhd_correct a r
      have ih_s' := DBhd_correct a s

      rw [union_congr (concat_congr ih_r ih_s') (concat_congr ih_r' ih_s)]

  | .etop =>
      rw [sem, der_top, D, sem, sem, sem, sem]
  | .inter r s =>
      rw [sem, der_inter, D, sem]
      have ih_r := D_correct a r
      have ih_s := D_correct a s
      rw [intersection_congr ih_r ih_s]
  | .sub r s =>
      rw [sem, der_diff, D, sem]
      have ih_r := D_correct a r
      have ih_s := D_correct a s
      rw [diff_congr ih_r ih_s]
  | .star r =>
      rw [sem, der_kstar, D, sem, sem]
      have ih_r  := D_correct a r
      have ih_r' := DBhd_correct a r
      rw [concat_congr ih_r (kstar_congr ih_r')]
  | .lookbehind r =>
      rw [sem, der_lookbehind, D, sem]
  | .lookahead r =>
      rw [sem, der_lookahead, D, sem]


theorem DAhd_correct {α} [DecidableEq α] (a : α) (r : RE α)
    : derLAhd a ⟦ r ⟧ ≐ ⟦ DAhd a r ⟧ := by
  intro t
  match r with
  | .symbol b =>
      rw [sem, derLAhd_symb, DAhd, sem]
  | .zero =>
      rw [sem, derLAhd_empty, DAhd, sem]
  | .plus r s =>
      rw [sem, derLAhd_union, DAhd, sem]
      have ih_r := DAhd_correct a r
      have ih_s := DAhd_correct a s
      rw [union_congr ih_r ih_s]
  | .one =>
      rw [sem, derLAhd_unit, DAhd, sem, sem]
  | .mult r s =>
      rw [sem, derLAhd_concat, DAhd, sem]
      have ih_r := DAhd_correct a r
      have ih_s := DAhd_correct a s
      rw [concat_congr ih_r ih_s]
  | .etop =>
      rw [sem, derLAhd_top, DAhd, sem, sem]
  | .inter r s =>
      rw [sem, derLAhd_inter, DAhd, sem]
      have ih_r := DAhd_correct a r
      have ih_s := DAhd_correct a s
      rw [intersection_congr ih_r ih_s]
  | .sub r s =>
      rw [sem, derLAhd_diff, DAhd, sem]
      have ih_r := DAhd_correct a r
      have ih_s := DAhd_correct a s
      rw [diff_congr ih_r ih_s]
  | .star r =>
      rw [sem, derLAhd_kstar, DAhd, sem, sem]
  | .lookbehind r =>
      rw [sem, derLAhd_lookbehind, DAhd]
      exact DAhd_correct a r t
  | .lookahead r =>
      rw [sem, derLAhd_lookahead, DAhd, sem]
      have ih_r := D_correct a r
      rw [lookahead_congr ih_r]

end



theorem wDBhd_correct [DecidableEq α] (w : List α) (r : RE α)
        : wderLBhd w ⟦ r ⟧ ≐ ⟦ wDBhd w r ⟧ := by
  intro u
  match w with
  | [] => rw [wderLBhd, wDBhd]
  | a :: w =>
      rw [wderLBhd, wDBhd]
      rw [wderLBhd_congr (DBhd_correct a r) w]
      rw [wDBhd_correct]

theorem wD_correct [DecidableEq α] (w : List α) (r : RE α)
        : wder w ⟦ r ⟧ ≐ ⟦ wD w r ⟧ := by
  intro u
  match w with
  | [] => rw [wder, wD]
  | a :: w =>
      rw [wder, wD]
      rw [wder_congr (D_correct a r) w]
      rw [wD_correct]

theorem wDAhd_correct [DecidableEq α] (w : List α) (r : RE α)
        : wderLAhd w ⟦ r ⟧ ≐ ⟦ wDAhd w r ⟧ := by
  intro u
  match w with
  | [] => rw [wderLAhd, wDAhd]
  | a :: w =>
      rw [wderLAhd, wDAhd]
      rw [wderLAhd_congr (DAhd_correct a r) w]
      rw [wDAhd_correct]


theorem tD_correct [DecidableEq α] (t : Triple α) (r : RE α) : tder t ⟦ r ⟧ ≐ ⟦ tD t r ⟧ := by
  intro u
  rw [tder, tD]
  simp

  have eq := wder_congr (wDBhd_correct (behind t) r) (mtch t)
  rw [wderLAhd_congr eq]

  have eq' := wD_correct (mtch t) (wDBhd (behind t) r)
  rw [wderLAhd_congr eq']

  have eq'' := wDAhd_correct (ahead t) (wD (mtch t) (wDBhd (behind t) r))
  rw [eq'']


theorem xD_correct [DecidableEq α] (a : α) (r : RE α) : xder a ⟦ r ⟧ ≐ ⟦ xD a r ⟧ := by
  intro t
  rw [xder, xD, sem, sem]
  rw [union, union, union, union]
  rw [DBhd_correct a r, D_correct a r, DAhd_correct a r]

theorem wxD_correct [DecidableEq α] (w : List α) (r : RE α) : wxder w ⟦ r ⟧ ≐ ⟦ wxD w r ⟧ := by
  intro t
  match w with
  | [] => rw [wxder, wxD]
  | a :: w =>
      rw [wxder, wxD]
      rw [wxder_congr (xD_correct a r) w]
      rw [wxD_correct w (xD a r)]

-------------------------------------------------------------------------

theorem N_tD_iff_mem {α} [DecidableEq α] : ∀ (t : Triple α) (r : RE α),
                                             N (tD t r) ↔ ⟦ r ⟧ t := by
  intro t r
  rw [←N_correct]
  rw [←nlbl_congr (tD_correct t r)]
  rw [nlbl_tder_iff_lang_mem]


theorem N_wxD_iff_exists {α} [DecidableEq α]
                         : ∀ (u : List α) (r : RE α),
                             N (wxD u r) ↔ ∃ x y z, u = x ++ y ++ z ∧ ⟦ r ⟧ (x, y, z) := by
  intro u r
  rw [←N_correct]
  rw [←nlbl_congr (wxD_correct u r)]
  rw [exists_mem_iff_wxder_nlbl]

--------------------------------------------------

def decideMem [DecidableEq α] (t : Triple α) (r : RE α) : Decidable (⟦ r ⟧ t) := by
  if h : N (tD t r) then
    apply isTrue
    rw [←N_tD_iff_mem]
    exact h
  else
    apply isFalse
    rw [←N_tD_iff_mem]
    exact h


def decideExists [DecidableEq α] (w : List α) (r : RE α)
    : Decidable (∃ (x y z : List α), w = x ++ y ++ z ∧ ⟦ r ⟧ ⟨x, y, z⟩) := by
  if h : N (wxD w r) then
    apply isTrue
    rw [←N_wxD_iff_exists]
    exact h
  else
    apply isFalse
    rw [←N_wxD_iff_exists]
    exact h

#print axioms decideExists
