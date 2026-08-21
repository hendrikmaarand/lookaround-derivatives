import LookaroundDerivatives.Triple
import LookaroundDerivatives.Expressions


theorem wD_append {α} [DecidableEq α]
                  : ∀ (u v : List α) (e : RE α), wD (u ++ v) e = wD v (wD u e) := by
  intro u v e
  match u with
  | [] => simp only [List.nil_append, wD]
  | a :: u => simp only [List.cons_append, wD]
              rw [wD_append u v (D a e)]

theorem wDBhd_append {α} [DecidableEq α]
                     : ∀ (u v : List α) (e : RE α), wDBhd (u ++ v) e = wDBhd v (wDBhd u e) := by
  intro u v e
  match u with
  | [] => simp only [List.nil_append, wDBhd]
  | a :: u => simp only [List.cons_append, wDBhd]
              rw [wDBhd_append u v (DBhd a e)]

theorem wDAhd_append {α} [DecidableEq α]
                     : ∀ (u v : List α) (e : RE α), wDAhd (u ++ v) e = wDAhd v (wDAhd u e) := by
  intro u v e
  match u with
  | [] => simp only [List.nil_append, wDAhd]
  | a :: u => simp only [List.cons_append, wDAhd]
              rw [wDAhd_append u v (DAhd a e)]

------------------------------------------------------------------------

def extractLAhd {α} [DecidableEq α] (a : α) (e : RE α) : RE α :=
  match e with
  | .symbol b => `0
  | .zero => `0
  | .plus e f => have e' := extractLAhd a e
                 have f' := extractLAhd a f
                 e' `+ f'
  | .one =>`◁ `1 `· ⊤
  | .mult e f => have e' := extractLAhd a e
                 have f' := extractLAhd a f
                 e' & f'
  | .etop => `◁ `1 `· ⊤
  | .inter e f => have e' := extractLAhd a e
                  have f' := extractLAhd a f
                  e' & f'
  | .sub e f => have e' := extractLAhd a e
                have f' := extractLAhd a f
                e' `- f'
  | .star e => `◁ `1 `· ⊤
  | .lookbehind e => extractLAhd a e
  | .lookahead e => D a e


theorem DAhd_exists {α} [DecidableEq α] : ∀ (a : α) (e : RE α), DAhd a e ≡ `▷ (extractLAhd a e) := by
  intro a e
  match e with
  | .symbol b =>
      rw [DAhd, extractLAhd]
      exact .sym .lahdZero

  | .zero =>
      rw [DAhd, extractLAhd]
      exact .sym .lahdZero

  | .plus e f =>
      have ih_e := DAhd_exists a e
      have ih_f := DAhd_exists a f
      rw [DAhd, extractLAhd]
      exact Equiv.trans (.plusCong ih_e ih_f)
                        .lahdPlus

  | .one =>
      rw [DAhd, extractLAhd]
      exact .lbhdUnit

  | .mult e f =>
      rw [DAhd, extractLAhd]
      have ih_e := DAhd_exists a e
      have ih_f := DAhd_exists a f
      apply Equiv.trans (.multCong ih_e ih_f)
      apply Equiv.trans .lahdMultInter
      exact .lahdInter

  | .etop =>
      rw [DAhd, extractLAhd]
      exact .lbhdUnit
  | .inter e f =>
      rw [DAhd, extractLAhd]
      have ih_e := DAhd_exists a e
      have ih_f := DAhd_exists a f
      exact Equiv.trans (.interCong ih_e ih_f)
                        .lahdInter
  | .sub e f =>
      rw [DAhd, extractLAhd]
      have ih_e := DAhd_exists a e
      have ih_f := DAhd_exists a f
      exact Equiv.trans (.subCong ih_e ih_f)
                        .lahdSub
  | .star e =>
      rw [DAhd, extractLAhd]
      exact .lbhdUnit
  | .lookbehind e =>
      rw [DAhd, extractLAhd]
      exact DAhd_exists a e
  | .lookahead e =>
      rw [DAhd, extractLAhd]
      exact .refl rfl


mutual

theorem DBhd_cong [DecidableEq α] : ∀ {a : α} {e f : RE α}, e ≡ f → DBhd a e ≡ DBhd a f := by
  intro a e f eq
  match eq with
  | .plusIdem  => rw [DBhd]; exact .plusIdem
  | .plusComm  => rw [DBhd, DBhd]; exact .plusComm
  | .plusAssoc => rw [DBhd, DBhd, DBhd, DBhd]; exact .plusAssoc

  | .plusZeroL => rw [DBhd, DBhd]; exact .plusZeroL

  | .multZeroL => rw [DBhd, DBhd, DBhd]; exact .multZeroL
  | .multZeroR => rw [DBhd, DBhd, DBhd]; exact .multZeroR

  | .interIdem => rw [DBhd]; exact .interIdem
  | .interComm => rw [DBhd, DBhd]; exact .interComm

  | .subZeroL => rw [DBhd, DBhd, DBhd]; exact .subZeroL

  | .lbhdZero => rw [DBhd, DBhd, D]; exact .lbhdZero
  | .lbhdUnit =>
      rw [DBhd, D, DBhd, DBhd, DBhd, DBhd, D]
      apply Equiv.trans .lbhdZero
      apply Equiv.trans (.sym .lahdZero)
      apply Equiv.lahdCong
      apply Equiv.trans (.sym .multZeroL)
      exact .multCong (.sym .lbhdZero) (.refl rfl)

  | .lahdZero => rw [DBhd, DBhd, DBhd]; exact .lahdZero
  | .lahdInter => rw [DBhd, DBhd, DBhd, DBhd, DBhd]
                  exact .lahdInter
  | .lahdPlus => rw [DBhd, DBhd, DBhd, DBhd, DBhd]
                 exact .lahdPlus
  | .lahdSub => rw[DBhd, DBhd, DBhd, DBhd, DBhd]
                exact .lahdSub

  | .lahdMultAssoc => rw [DBhd, DBhd, DBhd, DBhd]
                      exact Equiv.lahdMultAssoc

  | .lahdMultInter => rw [DBhd, DBhd, DBhd, DBhd]
                      exact .lahdMultInter

  | .distrL => rw [DBhd, DBhd, DBhd, DBhd, DBhd]
               exact .distrL

  | .refl eq => exact Equiv.refl (congrArg (DBhd a) eq)
  | .sym  eq  => exact .sym (DBhd_cong eq)
  | .trans eq₁ eq₂  => exact .trans (DBhd_cong eq₁) (DBhd_cong eq₂)

  | .plusCong r_eq s_eq => apply Equiv.plusCong (DBhd_cong r_eq) (DBhd_cong s_eq)
  | .multCong r_eq s_eq => apply Equiv.multCong (DBhd_cong r_eq) (DBhd_cong s_eq)
  | .interCong r_eq s_eq => apply Equiv.interCong (DBhd_cong r_eq) (DBhd_cong s_eq)
  | .subCong r_eq s_eq  => apply Equiv.subCong (DBhd_cong r_eq) (DBhd_cong s_eq)
  | .starCong r_eq => apply Equiv.starCong (DBhd_cong r_eq)
  | .lbhdCong r_eq => rw [DBhd, DBhd]
                      exact .lbhdCong (D_cong r_eq)
  | .lahdCong r_eq => rw [DBhd, DBhd]
                      exact Equiv.lahdCong (DBhd_cong r_eq)


theorem DAhd_cong [DecidableEq α] : ∀ {a : α} {e f : RE α}, e ≡ f → DAhd a e ≡ DAhd a f := by
  intro a e f eq
  match eq with
  | .plusIdem  => rw [DAhd]; exact .plusIdem
  | .plusComm  => rw [DAhd, DAhd]; exact .plusComm
  | .plusAssoc => rw [DAhd, DAhd, DAhd, DAhd]; exact .plusAssoc

  | .plusZeroL => rw [DAhd, DAhd]; exact .plusZeroL

  | .multZeroL => rw [DAhd, DAhd, DAhd]; exact .multZeroL
  | .multZeroR => rw [DAhd, DAhd, DAhd]; exact .multZeroR

  | .interIdem => rw [DAhd]; exact .interIdem
  | .interComm => rw [DAhd, DAhd]; exact .interComm

  | .subZeroL => rw [DAhd, DAhd, DAhd]; exact .subZeroL

  | .lbhdZero => rw [DAhd, DAhd, DAhd]; exact .refl rfl
  | .lbhdUnit =>
      calc  DAhd a `◁`1
        _ ≡ `◁ `1                          := .refl rfl
        _ ≡ `▷ (`◁ `1 `· ⊤)                := .lbhdUnit
        _ ≡ `▷ (`◁ `1 `· `◁ `1 `· ⊤)       := .lahdCong lbhd_unit_mult_idem
        _ ≡ `▷ (`0 `+ `◁ `1 `· `◁ `1 `· ⊤) := .lahdCong (.sym .plusZeroL)

        _ ≡ `▷(`0 `· DBhd a ⊤ `+ `◁ `1 `· `◁ `1 `· ⊤) :=
          .lahdCong (.plusCong (.sym .multZeroL) (.refl rfl))

        _ ≡ DAhd a `▷(`◁`1 `· ⊤) :=
          .refl rfl

  | .lahdZero => rw [DAhd, DAhd, D]; exact .lahdZero
  | .lahdInter => rw [DAhd, DAhd, DAhd, DAhd, D]
                  exact .lahdInter
  | .lahdPlus => rw [DAhd, DAhd, DAhd, DAhd, D]
                 exact .lahdPlus
  | .lahdSub => rw [DAhd, DAhd, DAhd, DAhd, D]
                exact .lahdSub

  | .lahdMultAssoc => rw [DAhd, DAhd, DAhd, DAhd]; exact .lahdMultAssoc

  | @Equiv.lahdMultInter _ r1 r2 =>
      calc DAhd a (`▷ r1 `· `▷ r2)
        _ ≡ `▷ (D a r1) `· `▷ (D a r2)      := .refl rfl
        _ ≡ `▷ (D a r1) & `▷ (D a r2)       := .lahdMultInter
        _ ≡ DAhd a (`▷ r1) & DAhd a (`▷ r2) := .refl rfl
        _ ≡ DAhd a (`▷ r1 & `▷ r2)          := .refl rfl

  | .distrL => rw [DAhd, DAhd, DAhd, DAhd, DAhd]
               exact .distrL

  | .refl eq => exact Equiv.refl (congrArg (DAhd a) eq)
  | .sym  eq => exact .sym (DAhd_cong eq)
  | .trans eq₁ eq₂ => exact .trans (DAhd_cong eq₁) (DAhd_cong eq₂)

  | .plusCong r_eq s_eq => apply Equiv.plusCong (DAhd_cong r_eq) (DAhd_cong s_eq)
  | .multCong r_eq s_eq => apply Equiv.multCong (DAhd_cong r_eq) (DAhd_cong s_eq)
  | .interCong r_eq s_eq => apply Equiv.interCong (DAhd_cong r_eq) (DAhd_cong s_eq)
  | .subCong r_eq s_eq => apply Equiv.subCong (DAhd_cong r_eq) (DAhd_cong s_eq)
  | .starCong r_eq => exact .refl rfl
  | .lbhdCong r_eq => rw [DAhd, DAhd]; exact (DAhd_cong r_eq)
  | .lahdCong r_eq => rw [DAhd, DAhd]
                      exact .lahdCong (D_cong r_eq)


theorem D_cong [DecidableEq α] : ∀ {a : α} {e f : RE α}, e ≡ f → D a e ≡ D a f := by
  intro a e f eq
  match eq with
  | .plusIdem  => rw [D]; exact .plusIdem
  | .plusComm  => rw [D, D]; exact .plusComm
  | .plusAssoc => rw [D, D, D, D]; exact .plusAssoc

  | .plusZeroL => rw [D, D]; exact .plusZeroL

  | @Equiv.multZeroL _ r =>
      calc D a (`0 `· r)
        _ ≡ `0 `· (DBhd a r) `+ `0 `· (D a r) := .refl rfl
        _ ≡ `0 `+ `0                          := .plusCong .multZeroL .multZeroL
        _ ≡ D a `0                            := .sym .plusIdem

  | @Equiv.multZeroR _ r => calc D a (r `· `0)
        _ ≡ (D a r) `· `0 `+ (DAhd a r) `· `0 := .refl rfl
        _ ≡ `0 `+ `0                          := .plusCong .multZeroR .multZeroR
        _ ≡ D a `0                            := .sym .plusIdem

  | .interIdem => exact .interIdem
  | .interComm => rw [D, D]; exact .interComm

  | @Equiv.subZeroL _ r =>
       calc D a (`0 `- r)
         _ ≡ `0 `- D a r := .refl rfl
         _ ≡ D a `0 := .subZeroL

  | .lbhdZero => rw [D, D]; exact .refl rfl
  | .lbhdUnit => exact .refl rfl

  | .lahdZero => rw [D, D]; exact .refl rfl
  | .lahdInter =>
      rw [D, D, D, D]
      apply Equiv.sym
      exact .interIdem
  | .lahdPlus => rw [D, D, D, D]
                 exact .plusZeroL
  | .lahdSub => rw [D, D, D, D]
                exact .subZeroL

  | @Equiv.lahdMultAssoc _ r₁ r₂ r₃ =>
      calc D a (`▷ r₁ `· `▷ r₂ `· r₃)
        _ ≡ `0 `· DBhd a (`▷r₂ `· r₃) `+ DAhd a `▷r₁ `· D a (`▷r₂ `· r₃) :=
          .refl rfl

        _ ≡ DAhd a `▷r₁ `· D a (`▷r₂ `· r₃) :=
          .trans (.plusCong .multZeroL (.refl rfl))
                 .plusZeroL
        _ ≡ DAhd a `▷r₁ `· DAhd a `▷r₂ `· D a r₃ :=
          .multCong (.refl rfl)
                    (.trans (.plusCong .multZeroL (.refl rfl))
                            .plusZeroL)

        _ ≡ `▷ (D a r₁) `· `▷ (D a r₂) `· D a r₃ :=
          .refl rfl

        _ ≡ (`▷ (D a r₁) `· `▷ (D a r₂)) `· D a r₃ :=
          .lahdMultAssoc

        _ ≡ DAhd a (`▷ r₁ `· `▷ r₂) `· D a r₃ :=
          .refl rfl

        _ ≡ `0 `· DBhd a r₃ `+ DAhd a (`▷ r₁ `· `▷ r₂) `· D a r₃ :=
          .trans (.sym .plusZeroL)
                 (.plusCong (.sym .multZeroL)
                            (.refl rfl))

        _ ≡ (D a (`▷ r₁ `· `▷ r₂)) `· DBhd a r₃ `+ DAhd a (`▷ r₁ `· `▷ r₂) `· D a r₃ :=
          .plusCong (.multCong (.trans .plusIdem
                                       (.plusCong (.sym .multZeroL) (.sym .multZeroR)))
                               (.refl rfl))
                    (.refl rfl)

        _ ≡ D a ((`▷ r₁ `· `▷ r₂) `· r₃) := .refl rfl

  | .lahdMultInter =>
      rw [D, D, D, D]
      apply Equiv.trans (.plusCong .multZeroL .multZeroR)
      apply Equiv.trans (.sym .plusIdem)
      exact .interIdem

  | @Equiv.distrL _ r s t =>
      calc D a (r `· (s `+ t))

        _ ≡ D a r `· DBhd a (s `+ t) `+ DAhd a r `· D a (s `+ t) := .refl rfl

        _ ≡ D a r `· (DBhd a s `+ DBhd a t) `+ DAhd a r `· (D a s `+ D a t) := .refl rfl

        _ ≡ (D a r `· DBhd a s `+ D a r `· DBhd a t) `+ (DAhd a r `· D a s `+ DAhd a r `· D a t) :=
            .plusCong .distrL .distrL

        _ ≡ D a r `· DBhd a s `+ (D a r `· DBhd a t `+ (DAhd a r `· D a s `+ DAhd a r `· D a t)) :=
            .sym .plusAssoc

        _ ≡ D a r `· DBhd a s `+ ((D a r `· DBhd a t `+ DAhd a r `· D a s) `+ DAhd a r `· D a t) :=
            .plusCong (.refl rfl) .plusAssoc

        _ ≡ D a r `· DBhd a s `+ ((DAhd a r `· D a s `+ D a r `· DBhd a t) `+ DAhd a r `· D a t) :=
            .plusCong (.refl rfl) (.plusCong .plusComm (.refl rfl))

        _ ≡ D a r `· DBhd a s `+ (DAhd a r `· D a s `+ (D a r `· DBhd a t `+ DAhd a r `· D a t)) :=
            .plusCong (.refl rfl) (.sym .plusAssoc)

        _ ≡ (D a r `· DBhd a s `+ DAhd a r `· D a s) `+ (D a r `· DBhd a t `+ DAhd a r `· D a t) :=
            .plusAssoc

        _ ≡ D a (r `· s `+ r `· t) := .refl rfl

  | .refl eq => exact Equiv.refl (congrArg (D a) eq)
  | .sym  eq => exact .sym (D_cong eq)
  | .trans eq₁ eq₂ => exact .trans (D_cong eq₁) (D_cong eq₂)

  | .plusCong r_eq s_eq => apply Equiv.plusCong (D_cong r_eq) (D_cong s_eq)
  | @Equiv.multCong _ r r' s s' r_eq s_eq =>
      calc  D a (r `· s)
        _ ≡ (D a r) `· (DBhd a s) `+ (DAhd a r) `· (D a s) :=
          .refl rfl
        _ ≡ (D a r') `· (DBhd a s') `+ (DAhd a r') `· (D a s') :=
          .plusCong (.multCong (D_cong r_eq) (DBhd_cong s_eq))
                    (.multCong (DAhd_cong r_eq) (D_cong s_eq))
        _ ≡ D a (r' `· s') := .refl rfl
  | .interCong r_eq s_eq => apply Equiv.interCong (D_cong r_eq) (D_cong s_eq)
  | .subCong r_eq s_eq => apply Equiv.subCong (D_cong r_eq) (D_cong s_eq)
  | .starCong r_eq =>
      rw [D, D]
      exact .multCong (D_cong r_eq) (.starCong (DBhd_cong r_eq))
  | .lbhdCong r_eq => exact .refl rfl
  | .lahdCong r_eq => exact .refl rfl

end





theorem wDBhd_cong [DecidableEq α]
                   : ∀ {w : List α} {e f : RE α}, e ≡ f → wDBhd w e ≡ wDBhd w f := by
  intro w e f eq
  induction w generalizing e f with
  | nil => exact eq
  | cons a w ih => rw [wDBhd, wDBhd]
                   apply ih
                   exact DBhd_cong eq


theorem wDAhd_cong [DecidableEq α]
                   : ∀ {w : List α} {e f : RE α}, e ≡ f → wDAhd w e ≡ wDAhd w f := by
  intro w e f eq
  induction w generalizing e f with
  | nil => exact eq
  | cons a w ih => rw [wDAhd, wDAhd]
                   apply ih
                   exact DAhd_cong eq


theorem wD_cong [DecidableEq α]
                   : ∀ {w : List α} {e f : RE α}, e ≡ f → wD w e ≡ wD w f := by
  intro w e f eq
  induction w generalizing e f with
  | nil => exact eq
  | cons a w ih => rw [wD, wD]
                   apply ih
                   exact D_cong eq


----------------------------------------------------------------------------------


theorem D_after_DAhd_is_zero {α} [DecidableEq α]
                             : ∀ (a b : α) (e : RE α), D b (DAhd a e) ≡ `0 := by
  intro a b e
  let e' := extractLAhd a e
  calc D b (DAhd a e)
    _ ≡ D b (`▷ e') := D_cong (DAhd_exists a e)
    _ ≡ `0          := .refl rfl




theorem D_after_ne_wDAhd_is_zero {α} [DecidableEq α]
                                 : ∀ (a : α) {w : List α} (ne : ¬ w = []) (e : RE α),
                                     D a (wDAhd w e) ≡ `0 := by
  intro a w ne e
  match w with
  | [] => contradiction
  | b :: [] =>
      rw [wDAhd, wDAhd]
      exact D_after_DAhd_is_zero b a e
  | b :: c :: w =>
      rw [wDAhd]
      apply D_after_ne_wDAhd_is_zero
      simp

theorem D_after_wDAhd_is_zero_list [DecidableEq α]
                                   (a : α) (e : RE α)
                                   {ws : List (List α)} (ne : ¬ ws = [])
                                   (h : ∀ w ∈ ws, ¬ w = [])
                                   : D a (List.foldl (flip wDAhd) e ws) ≡ `0 := by
  match ws with
  | [] => contradiction
  | w :: [] =>
      rw [List.foldl, flip, List.foldl]
      apply D_after_ne_wDAhd_is_zero
      apply h
      simp
  | w :: w' :: ws =>
      rw [List.foldl, flip]
      apply D_after_wDAhd_is_zero_list a (wDAhd w e) (by simp)
      intro y y_in
      simp [h, y_in]



theorem DBhd_after_D_is_zero {α} [DecidableEq α]
                             : ∀ (a b : α) (e : RE α), DBhd b (D a e) ≡ `0 := by
  intro a b e
  match e with
  | .symbol c =>
      rw [D]
      if h : a = c then
        simp [h, DBhd, D]
        exact .lbhdZero
      else
        simp [h, DBhd]
        exact .refl rfl
  | .zero =>
      rw [D, DBhd]
      exact .refl rfl
  | .plus e f =>
      rw [D, DBhd]
      have ih_e := DBhd_after_D_is_zero a b e
      have ih_f := DBhd_after_D_is_zero a b f
      apply Equiv.trans (.plusCong ih_e ih_f)
      exact .plusZeroL
  | .one =>
      rw [D, DBhd]
      exact .refl rfl
  | .mult e f =>
      calc DBhd b (D a (e `· f))
        _ ≡ DBhd b (D a e `· DBhd a f `+ DAhd a e `· D a f)
          := .refl rfl
        _ ≡ DBhd b (D a e) `· DBhd b (DBhd a f) `+ DBhd b (DAhd a e) `· DBhd b (D a f)
          := .refl rfl
        _ ≡ `0 `· DBhd b (DBhd a f) `+ DBhd b (DAhd a e) `· `0
          := .plusCong (.multCong (DBhd_after_D_is_zero a b e) (.refl rfl))
                       (.multCong (.refl rfl) (DBhd_after_D_is_zero a b f))
        _ ≡ `0 `+ `0
          := .plusCong .multZeroL .multZeroR
        _ ≡ `0
          := .sym .plusIdem

  | .etop =>
      rw [D, DBhd, DBhd, DBhd, D]
      apply Equiv.trans (.multCong .lbhdZero (.refl rfl))
      exact .multZeroL

  | .inter e f =>
      rw [D, DBhd]
      have ih_e := DBhd_after_D_is_zero a b e
      have ih_f := DBhd_after_D_is_zero a b f
      apply Equiv.trans (.interCong ih_e ih_f)
      exact .sym .interIdem

  | .sub e f =>
      rw [D, DBhd]
      have ih_e := DBhd_after_D_is_zero a b e
      have ih_f := DBhd_after_D_is_zero a b f
      apply Equiv.trans (.subCong ih_e ih_f)
      exact .subZeroL


  | .star e =>
      rw [D, DBhd]
      apply Equiv.trans (.multCong (DBhd_after_D_is_zero a b e) (.refl rfl))
      exact .multZeroL

  | .lookbehind e =>
      rw [D, DBhd]
      exact .refl rfl

  | .lookahead e =>
      rw [D, DBhd]
      exact .refl rfl


theorem DBhd_after_DAhd_is_zero {α} [DecidableEq α]
                                : ∀ (a b : α) (e : RE α), DBhd b (DAhd a e) ≡ `0 := by
  intro a b e
  match e with
  | .symbol c =>
      rw [DAhd, DBhd]
      exact .refl rfl
  | .zero =>
      rw [DAhd, DBhd]
      exact .refl rfl
  | .plus e f =>
      rw [DAhd, DBhd]
      have ih_e := DBhd_after_DAhd_is_zero a b e
      have ih_f := DBhd_after_DAhd_is_zero a b f
      apply Equiv.trans (.plusCong ih_e ih_f)
      exact .plusZeroL
  | .one =>
      rw [DAhd, DBhd, D]
      exact .lbhdZero
  | .mult e f =>
      rw [DAhd, DBhd]
      have ih_e := DBhd_after_DAhd_is_zero a b e
      apply Equiv.trans (.multCong ih_e (.refl rfl))
      exact .multZeroL

  | .etop =>
      rw [DAhd, DBhd, D]
      exact .lbhdZero

  | .inter e f =>
      rw [DAhd, DBhd]
      have ih_e := DBhd_after_DAhd_is_zero a b e
      have ih_f := DBhd_after_DAhd_is_zero a b f
      apply Equiv.trans (.interCong ih_e ih_f)
      exact .sym .interIdem

  | .sub e f =>
      rw [DAhd, DBhd]
      have ih_e := DBhd_after_DAhd_is_zero a b e
      have ih_f := DBhd_after_DAhd_is_zero a b f
      apply Equiv.trans (.subCong ih_e ih_f)
      exact .subZeroL


  | .star e =>
      rw [DAhd, DBhd, D]
      exact .lbhdZero

  | .lookbehind e =>
      rw [DAhd]
      apply DBhd_after_DAhd_is_zero

  | .lookahead e =>
      rw [DAhd, DBhd]
      apply Equiv.trans (.lahdCong (DBhd_after_D_is_zero a b e))
      exact .lahdZero
