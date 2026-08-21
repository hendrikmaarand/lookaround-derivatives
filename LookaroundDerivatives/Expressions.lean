import LookaroundDerivatives.Triple
import LookaroundDerivatives.Lists

inductive RE (α : Type) : Type where
  | symbol : α → RE α
  | zero : RE α
  | plus : RE α → RE α → RE α
  | one : RE α
  | mult : RE α → RE α → RE α
  | etop : RE α
  | inter : RE α → RE α → RE α
  | sub : RE α → RE α → RE α
  | star : RE α → RE α
  | lookbehind : RE α → RE α
  | lookahead  : RE α → RE α
  deriving Repr, DecidableEq

prefix:max "`$" => RE.symbol
notation "`0" => RE.zero
notation "⊤" => RE.etop
infixr:55 " `+ " => RE.plus
notation "`1" => RE.one
infixr:60 " `· " => RE.mult
infixr:55 " & " => RE.inter
infixl:55 " `- " => RE.sub
postfix:max "*" => RE.star
prefix:max "`◁" => RE.lookbehind
prefix:max "`▷" => RE.lookahead


def N (r : RE α) : Bool :=
  match r with
  | .symbol b     => false
  | .zero         => false
  | .plus r s     => N r || N s
  | .one          => true
  | .mult r s     => N r && N s
  | .etop         => true
  | .inter r s    => N r && N s
  | .sub r s      => N r && (! N s)
  | .star r       => true
  | .lookbehind r => N r
  | .lookahead r  => N r



mutual

def DBhd [DecidableEq α] (a : α) (r : RE α) : RE α :=
  match r with
  | .symbol b     => `$ b
  | .zero         => `0
  | .plus r s     => DBhd a r `+ DBhd a s
  | .one          => `1
  | .mult r s     => DBhd a r `· DBhd a s
  | .etop         => ⊤
  | .inter r s    => DBhd a r & DBhd a s
  | .sub r s      => DBhd a r `- DBhd a s
  | .star r       => (DBhd a r)*
  | .lookbehind r => `◁ (D a r)
  | .lookahead r  => `▷ (DBhd a r)


def D [DecidableEq α] (a : α) (r : RE α) : RE α :=
  match r with
  | .symbol b     => if a = b then `◁ `1 else `0
  | .zero         => `0
  | .plus r s     => D a r `+ D a s
  | .one          => `0
  | .mult r s     => (D a r) `· (DBhd a s) `+ (DAhd a r) `· (D a s)
  | .etop         => `◁ `1 `· ⊤
  | .inter r s    => D a r & D a s
  | .sub r s      => D a r `- D a s
  | .star r       => D a r `· (DBhd a r)*
  | .lookbehind r => `0
  | .lookahead r  => `0

def DAhd [DecidableEq α] (a : α) (r : RE α) : RE α :=
  match r with
  | .symbol b     => `0
  | .zero         => `0
  | .plus r s     => DAhd a r `+ DAhd a s
  | .one          => `◁ `1
  | .mult r s     => DAhd a r `· DAhd a s
  | .etop         => `◁ `1
  | .inter r s    => DAhd a r & DAhd a s
  | .sub r s      => DAhd a r `- DAhd a s
  | .star r       => `◁ `1
  | .lookbehind r => DAhd a r
  | .lookahead r  => `▷ (D a r)

end


def wDBhd [DecidableEq α] (w : List α) (r : RE α) : RE α :=
  match w with
  | [] => r
  | a :: w => wDBhd w (DBhd a r)

def wD [DecidableEq α] (w : List α) (r : RE α) : RE α :=
  match w with
  | [] => r
  | a :: w => wD w (D a r)

def wDAhd [DecidableEq α] (w : List α) (r : RE α) : RE α :=
  match w with
  | [] => r
  | a :: w => wDAhd w (DAhd a r)



def tD [DecidableEq α] (t : Triple α) (r : RE α) : RE α :=
  (wDAhd (ahead t) ∘ wD (mtch t) ∘ wDBhd (behind t)) r


def xD [DecidableEq α] (a : α) (r : RE α) : RE α :=
  DBhd a r `+ D a r `+ DAhd a r

def wxD [DecidableEq α] (w : List α) (r : RE α) : RE α :=
  match w with
  | [] => r
  | a :: w => wxD w (xD a r)



--------------------------------------------------------------------
-- equivalence

inductive Equiv {α : Type} : RE α → RE α → Prop where
  | plusIdem : {r : RE α} → Equiv r (r `+ r)
  | plusComm : {r s : RE α} → Equiv (r `+ s) (s `+ r)
  | plusAssoc : {r s t : RE α} → Equiv (r `+ (s `+ t)) ((r `+ s) `+ t)

  | plusZeroL : {r : RE α} → Equiv (`0 `+ r) r

  | multZeroL : {r : RE α} → Equiv (`0 `· r) `0
  | multZeroR : {r : RE α} → Equiv (r `· `0) `0

  | interIdem : {r : RE α} → Equiv r (r & r)
  | interComm : {r s : RE α} → Equiv (r & s) (s & r)

  | subZeroL : {r : RE α} → Equiv (`0 `- r) `0

  | lbhdZero : Equiv (`◁ `0) `0
  | lbhdUnit : Equiv (`◁ `1) (`▷ (`◁ `1 `· ⊤))

  | lahdZero : Equiv (`▷ `0) `0
  | lahdInter : {r₁ r₂ : RE α} → Equiv (`▷ r₁ & `▷ r₂) (`▷ (r₁ & r₂))
  | lahdPlus : {r₁ r₂ : RE α} → Equiv (`▷ r₁ `+ `▷ r₂) (`▷ (r₁ `+ r₂))
  | lahdSub : {r₁ r₂ : RE α} → Equiv (`▷ r₁ `- `▷ r₂) (`▷ (r₁ `- r₂))

  | lahdMultAssoc : {r₁ r₂ r₃ : RE α} → Equiv (`▷ r₁ `· (`▷ r₂ `· r₃)) ((`▷ r₁ `· `▷ r₂) `· r₃)
  | lahdMultInter : {r₁ r₂ : RE α} → Equiv (`▷ r₁ `· `▷ r₂) (`▷ r₁ & `▷ r₂)

  | distrL : {r s t : RE α} → Equiv (r `· (s `+ t)) (r `· s `+ r `· t)

  | refl : {r s : RE α} → r = s → Equiv r s
  | sym  : {r s : RE α} → Equiv r s → Equiv s r
  | trans : {r s t : RE α} → Equiv r s → Equiv s t → Equiv r t

  -- congruences
  | plusCong : {r r' s s' : RE α} → Equiv r r' → Equiv s s' → Equiv (r `+ s) (r' `+ s')
  | multCong : {r r' s s' : RE α} → Equiv r r' → Equiv s s' → Equiv (r `· s) (r' `· s')
  | interCong : {r r' s s' : RE α} → Equiv r r' → Equiv s s' → Equiv (r & s) (r' & s')
  | subCong : {r r' s s' : RE α} → Equiv r r' → Equiv s s' → Equiv (r `- s) (r' `- s')
  | starCong : {r r' : RE α} → Equiv r r' → Equiv (r*) (r'*)
  | lahdCong : {r r' : RE α} → Equiv r r' → Equiv (`▷ r) (`▷ r')
  | lbhdCong : {r r' : RE α} → Equiv r r' → Equiv (`◁ r) (`◁ r')


infix:40 " ≡ " => Equiv

instance instEquiv {α} : Trans (Equiv : RE α → RE α → Prop) Equiv Equiv where
   trans p q := .trans p q


theorem plus_zero_r {r : RE α} : r `+ `0 ≡ r :=
  .trans .plusComm .plusZeroL


theorem lahd_mult_idem {r : RE α} : `▷ r ≡ `▷ r `· `▷ r :=
  .trans .interIdem (.sym .lahdMultInter)

theorem lahd_mult_comm {r s : RE α} : `▷ r `· `▷ s ≡ `▷ s `· `▷ r :=
  calc `▷ r `· `▷ s
    _ ≡ `▷ r & `▷ s := .lahdMultInter
    _ ≡ `▷ s & `▷ r := .interComm
    _ ≡ `▷ s `· `▷ r := .sym .lahdMultInter


theorem lbhd_unit_mult_idem {r : RE α} : `◁ `1 `· r ≡ `◁ `1 `· (`◁ `1 `· r) := by
  calc `◁`1 `· r
    _ ≡ `▷ (`◁ `1 `· ⊤) `· r                      := .multCong .lbhdUnit (.refl rfl)
    _ ≡ (`▷ (`◁ `1 `· ⊤) `· `▷ (`◁ `1 `· ⊤)) `· r := .multCong lahd_mult_idem (.refl rfl)
    _ ≡ `▷ (`◁ `1 `· ⊤) `· (`▷ (`◁ `1 `· ⊤) `· r) := .sym .lahdMultAssoc
    _ ≡ `◁`1 `· (`◁`1 `· r)                       := .multCong (.sym .lbhdUnit)
                                                               (.multCong (.sym .lbhdUnit)
                                                                          (.refl rfl))


theorem lbhd_unit_mult_idem' : `◁ (`1 : RE α) ≡ `◁ `1 `· `◁ `1 := by
  calc `◁ `1
    _ ≡ `▷ (`◁ `1 `· ⊤)                    := .lbhdUnit
    _ ≡ `▷ (`◁ `1 `· ⊤) & `▷ (`◁ `1 `· ⊤)  := .interIdem
    _ ≡ `▷ (`◁ `1 `· ⊤) `· `▷ (`◁ `1 `· ⊤) := .sym .lahdMultInter
    _ ≡ `◁ `1 `· `◁ `1                     := .multCong (.sym .lbhdUnit) (.sym .lbhdUnit)



--------------------------------------------------------------------

def toSum (rs : List (RE α)) : RE α :=
  match rs with
  | [] => `0
  | r :: rs => r `+ toSum rs


theorem D_toSum {α} [DecidableEq α]
                : ∀ (es : List (RE α)) (a : α),
                    D a (toSum es) ≡ toSum (List.map (D a) es) := by
  intro es a
  match es with
  | [] => simp [toSum, D]
          exact .refl rfl
  | e :: es =>
      simp [toSum, D]
      apply Equiv.plusCong (.refl rfl)
      apply D_toSum

theorem DAhd_toSum {α} [DecidableEq α]
                   : ∀ (es : List (RE α)) (a : α),
                       DAhd a (toSum es) ≡ toSum (List.map (DAhd a) es) := by
  intro es a
  match es with
  | [] => simp [toSum, DAhd]
          exact .refl rfl
  | e :: es =>
      simp [toSum, DAhd]
      apply Equiv.plusCong (.refl rfl)
      apply DAhd_toSum



theorem toSum_cons_equiv {α} {r s : RE α} {rs ss : List (RE α)}
                     : r ≡ s → toSum rs ≡ toSum ss →
                       toSum (r :: rs) ≡ toSum (s :: ss) := by
  intro r_eq rs_eq
  rw [toSum, toSum]
  exact .plusCong r_eq rs_eq

theorem toSum_map {α A} {f g : A → RE α}
                  (xs : List A)
                  (eq : ∀ x ∈ xs, f x ≡ g x)
                  : toSum (List.map f xs) ≡ toSum (List.map g xs) := by
  match xs with
  | [] => exact .refl rfl
  | x :: xs =>
      simp
      apply toSum_cons_equiv
      . exact eq x List.mem_cons_self
      . apply toSum_map xs (by intro x x_in; exact eq x (by simp [x_in]))


theorem toSum_append {xs ys : List (RE α)}
                     : toSum (xs ++ ys) ≡ toSum xs `+ toSum ys := by
  match xs with
  | [] => rw [List.nil_append, toSum]
          exact .sym .plusZeroL
  | x :: xs =>
      calc toSum (x :: xs ++ ys)
        _ ≡ x `+ toSum (xs ++ ys)       := by simp [toSum]; exact .refl rfl
        _ ≡ x `+ (toSum xs `+ toSum ys) := .plusCong (.refl rfl) toSum_append
        _ ≡ (x `+ toSum xs) `+ toSum ys := .plusAssoc
        _ ≡ toSum (x :: xs) `+ toSum ys := by simp [toSum]; exact .refl rfl


theorem toSum_map_append {xs : List A} {f g : A → RE α}
                         : toSum (List.map f xs) `+ toSum (List.map g xs)
                           ≡
                           toSum (List.map (λ x => f x `+ g x) xs) := by
  match xs with
  | [] => simp
          exact .sym .plusIdem

  | x :: xs => calc toSum (List.map f (x :: xs)) `+ toSum (List.map g (x :: xs))
      _ ≡ toSum (f x :: List.map f xs) `+ toSum (g x :: List.map g xs) :=
          .refl rfl

      _ ≡ (f x `+ toSum (List.map f xs)) `+ (g x `+ toSum (List.map g xs)) :=
          .refl rfl

      _ ≡ f x `+ (toSum (List.map f xs) `+ (g x `+ toSum (List.map g xs))) :=
          .sym .plusAssoc

      _ ≡ f x `+ ((toSum (List.map f xs) `+ g x) `+ toSum (List.map g xs)) :=
          .plusCong (.refl rfl) .plusAssoc

      _ ≡ f x `+ ((g x `+ toSum (List.map f xs)) `+ toSum (List.map g xs)) :=
          .plusCong (.refl rfl)
                    (.plusCong .plusComm (.refl rfl))

      _ ≡ f x `+ (g x `+ (toSum (List.map f xs) `+ toSum (List.map g xs))) :=
          .plusCong (.refl rfl)
                    (.sym .plusAssoc)

      _ ≡ (f x `+ g x) `+ (toSum (List.map f xs) `+ toSum (List.map g xs)) :=
          .plusAssoc

      _ ≡ (f x `+ g x) `+ toSum (List.map (fun x => f x `+ g x) xs) :=
          .plusCong (.refl rfl)
                    toSum_map_append

      _ ≡ toSum ((f x `+ g x) :: List.map (fun x => f x `+ g x) xs) :=
          .refl rfl

      _ ≡ toSum (List.map (fun x => f x `+ g x) (x :: xs)) :=
          .refl rfl


theorem toSum_dup {α} {x : RE α} {l : List (RE α)}
                   : x ∈ l → toSum (x :: l) ≡ toSum l := by
  induction l with
  | nil => simp
  | cons y l ih =>
      intro h
      simp only [toSum]
      rcases List.mem_cons.mp h with eq | mem
      · subst eq
        calc x `+ x `+ toSum l
          _ ≡ (x `+ x) `+ toSum l := .plusAssoc
          _ ≡ x `+ toSum l        := .plusCong (.sym .plusIdem) (.refl rfl)

      · calc x `+ y `+ toSum l
          _ ≡ (x `+ y) `+ toSum l := .plusAssoc
          _ ≡ (y `+ x) `+ toSum l := .plusCong .plusComm (.refl rfl)
          _ ≡ y `+ x `+ toSum l   := .sym .plusAssoc
          _ ≡ y `+ toSum (x :: l) := .plusCong (.refl rfl) (.refl rfl)
          _ ≡ y `+ toSum l        := .plusCong (.refl rfl) (ih mem)


theorem toSum_append_subset {α} {l₁ l₂ : List (RE α)}
                            (sub : ∀ x ∈ l₁, x ∈ l₂)
                            : toSum (l₁ ++ l₂) ≡ toSum l₂ := by
  induction l₁ with
  | nil => exact Equiv.refl rfl
  | cons x l₁ ih =>
      have hx : x ∈ l₁ ++ l₂ := List.mem_append_right l₁ (sub x List.mem_cons_self)

      calc toSum (x :: l₁ ++ l₂)
        _ ≡ toSum (l₁ ++ l₂) := toSum_dup hx
        _ ≡ toSum l₂         := ih (λ x' mem => sub x' (List.mem_cons_of_mem x mem))


theorem toSum_mem_eq {α} {l₁ l₂ : List (RE α)}
                     (eq : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
                     : toSum l₁ ≡ toSum l₂ := by
  calc toSum l₁
    _ ≡ toSum (l₂ ++ l₁)     := .sym (toSum_append_subset (λ x hx => (eq x).mpr hx))
    _ ≡ toSum l₂ `+ toSum l₁ := toSum_append
    _ ≡ toSum l₁ `+ toSum l₂ := .plusComm
    _ ≡ toSum (l₁ ++ l₂)     := .sym toSum_append
    _ ≡ toSum l₂             := toSum_append_subset (λ x hx => (eq x).mp hx)

--------------------------------------------------------------------

def toMult' (rs : List (RE α)) (r : RE α) :=
  match rs with
  | []       => r
  | r' :: rs => r' `· toMult' rs r


theorem toMult'_snoc {α} [DecidableEq α]
                     : ∀ (es : List (RE α)) (e e' : RE α),
                         toMult' (es ++ [e]) e' = toMult' es (e `· e') := by
  intro es e e'
  match es with
  | [] => rfl
  | g :: es =>
      rw [List.cons_append, toMult']
      rw [toMult']
      rw [toMult'_snoc]


theorem DAhd_toMult' {α} [DecidableEq α]
                     : ∀ (es : List (RE α)) (e : RE α) (a : α),
                         DAhd a (toMult' es e) = toMult' (List.map (DAhd a) es) (DAhd a e) := by
  intro es e a
  match es with
  | [] => rw [toMult', List.map_nil, toMult']

  | e :: es =>
      rw [toMult', List.map_cons, toMult', DAhd]
      rw [DAhd_toMult']

----------------------------------------------------------------------


def elemUpTo (e : RE α) (es : List (RE α)) : Prop :=
  ∃ e', e ≡ e' ∧ e' ∈ es

notation e " ≡∈ " es => elemUpTo e es


def subsetUpTo (es fs : List (RE α)) : Prop :=
  ∀ {e}, e ∈ es → e ≡∈ fs

notation es " ≡⊆ " fs => subsetUpTo es fs


theorem subsetUpTo_reprs {α} {es fs : List (RE α)}
                         (sub : es ≡⊆ fs)
                         : ∃ fs', List.length es = List.length fs' ∧
                                  fs' ⊆ fs ∧
                                  toSum es ≡ toSum fs' := by
  match es with
  | [] => exists []
          simp [toSum]
          exact .refl rfl
  | e :: es =>
      have ⟨f', eq, f'_in⟩ := sub List.mem_cons_self
      have sub' : es ≡⊆ fs := by
        intro e' e'_in
        exact sub (List.mem_cons_of_mem e e'_in)
      have ⟨fs', ls', ss', eq'⟩ := subsetUpTo_reprs sub'
      exists f' :: fs'
      constructor
      . simp [ls']
      . constructor
        . intro x x_in
          apply Or.elim (List.mem_cons.mp x_in)
          . intro eq
            simp [eq, f'_in]
          . apply ss'

        . exact toSum_cons_equiv eq eq'


theorem subsetUpTo_reprs' {α} {es fs : List (RE α)}
                          (sub : es ≡⊆ fs)
                          : ∃ fs', List.length es = List.length fs' ∧
                                   fs' ⊆ fs ∧
                                   ∀ (x : RE α), (x ≡∈ es) ↔ (x ≡∈ fs') := by
  match es with
  | [] => exists []
          simp

  | e :: es =>
      have ⟨f', eq, f'_in⟩ := sub List.mem_cons_self
      have sub' : es ≡⊆ fs := by
        intro e' e'_in
        exact sub (List.mem_cons_of_mem e e'_in)
      have ⟨fs', ls', ss', eq'⟩ := subsetUpTo_reprs' sub'

      exists f' :: fs'
      simp [ls', f'_in, ss']
      intro x
      constructor
      . intro ⟨x', x_eq, x'_in⟩
        apply Or.elim (List.mem_cons.mp x'_in)
        . intro x'_eq
          rw [x'_eq] at x_eq
          exists f'
          simp
          exact .trans x_eq eq

        . intro x'_in
          have ⟨x'', x'_eq, x''_in⟩ := (eq' x').mp ⟨x', .refl rfl, x'_in⟩
          exists x''
          simp [x''_in]
          exact .trans x_eq x'_eq

      . intro ⟨x', x_eq, x'_in⟩
        apply Or.elim (List.mem_cons.mp x'_in)
        . intro x'_eq
          rw [x'_eq] at x_eq
          exists e
          simp
          exact .trans x_eq (.sym eq)

        . intro x'_in
          have ⟨x'', x'_eq, x''_in⟩ := (eq' x').mpr ⟨x', .refl rfl, x'_in⟩
          exists x''
          simp [x''_in]
          exact .trans x_eq x'_eq



------------------------------------------------------------------------


theorem toMult'_dup {α} {rd b : RE α} {rs : List (RE α)}
                    (rs_ahd  : ∀ x ∈ rs,  ∃ x', x ≡ `▷ x')
                    (mem : rd ≡∈ rs)
                    : toMult' (rd :: rs) b ≡ toMult' rs b := by
  match rs with
  | [] => simp [elemUpTo] at mem
  | r :: rs =>
      obtain ⟨e, rd_eq, e_in⟩ := mem
      simp only [toMult']
      rcases List.mem_cons.mp e_in with eq | mem
      . subst eq
        have ⟨e', e_eq⟩ := rs_ahd e (by simp)
        calc rd `· e `· toMult' rs b
          _ ≡ `▷ e' `· `▷ e' `· toMult' rs b   := .multCong (.trans rd_eq e_eq)
                                                            (.multCong e_eq (.refl rfl))
          _ ≡ (`▷ e' `· `▷ e') `· toMult' rs b := .lahdMultAssoc

          _ ≡ `▷ e' `· toMult' rs b            := .multCong (.sym lahd_mult_idem) (.refl rfl)

          _ ≡ e `· toMult' rs b                := .multCong (.sym e_eq) (.refl rfl)

      . have ⟨e', e_eq⟩ := rs_ahd e (by simp [mem])
        have ⟨r', r_eq⟩ := rs_ahd r (by simp)

        calc rd `· r `· toMult' rs b
          _ ≡ `▷ e' `· `▷ r' `· toMult' rs b := .multCong (.trans rd_eq e_eq)
                                                          (.multCong r_eq (.refl rfl))
          _ ≡ (`▷ e' `· `▷ r') `· toMult' rs b := .lahdMultAssoc
          _ ≡ (`▷ r' `· `▷ e') `· toMult' rs b := .multCong lahd_mult_comm (.refl rfl)
          _ ≡ `▷ r' `· `▷ e' `· toMult' rs b := .sym .lahdMultAssoc
          _ ≡ r `· rd `· toMult' rs b := .multCong (.sym r_eq)
                                                   (.multCong (.sym (.trans rd_eq e_eq))
                                                              (.refl rfl))
          _ ≡ r `· toMult' rs b := .multCong (.refl rfl)
                                             (toMult'_dup (λ x x_rs => rs_ahd x (by simp [x_rs]))
                                                          ⟨e, rd_eq, mem⟩)


theorem toMult'_append_subset {α} {b : RE α}{rs rs' : List (RE α)}
                              (rs'_ahd  : ∀ x ∈ rs',  ∃ x', x ≡ `▷ x')
                              (sub : rs ≡⊆ rs')
                              : toMult' (rs ++ rs') b ≡ toMult' rs' b := by
  match rs with
  | [] => exact .refl rfl
  | r :: rs =>
      have r_in : r ≡∈ rs ++ rs' := by
        have ⟨r', eq, mem⟩ : r ≡∈ rs' := sub List.mem_cons_self
        exact ⟨r', eq, List.mem_append_right rs mem⟩

      have sub' : rs ≡⊆ rs' := by
        intro x x_in
        apply sub
        simp [x_in]

      have rs_ahd : ∀ x ∈ rs,  ∃ x', x ≡ `▷ x' := by
        intro x x_in
        have ⟨y, eq, mem⟩ := sub' x_in
        have ⟨x', eq'⟩ := rs'_ahd y mem
        exists x'
        exact .trans eq eq'

      have rs_rs'_ahd : ∀ x ∈ (rs ++ rs'),  ∃ x', x ≡ `▷ x' := by
        intro x x_in
        rcases List.mem_append.mp x_in with h | h
        . exact rs_ahd x h
        . exact rs'_ahd x h

      calc toMult' (r :: rs ++ rs') b
        _ ≡ toMult' (rs ++ rs') b := toMult'_dup rs_rs'_ahd r_in
        _ ≡ toMult' rs' b := toMult'_append_subset rs'_ahd sub'


theorem toMult'_slide {α} {rs ts : List (RE α)}{t b : RE α}
                      (rs_ahd  : ∀ x ∈ rs,  ∃ x', x ≡ `▷ x')
                      (ts_ahd  : ∀ x ∈ t :: ts,  ∃ x', x ≡ `▷ x')
                      : toMult' (rs ++ t :: ts) b ≡ toMult' (t :: rs ++ ts) b := by
  match rs with
  | [] => simp
          exact .refl rfl
  | r :: rs =>
      have ⟨r', r_eq⟩ := rs_ahd r List.mem_cons_self
      have ⟨t', t_eq⟩ := ts_ahd t List.mem_cons_self

      have rs_ahd' : ∀ x ∈ rs,  ∃ x', x ≡ `▷ x' := by
        intro x x_in
        apply rs_ahd
        simp [x_in]

      calc toMult' (r :: rs ++ t :: ts) b
        _ ≡ r `· toMult' (rs ++ t :: ts) b
          := .refl rfl

        _ ≡ r `· t `· toMult' (rs ++ ts) b
          := .multCong (.refl rfl)
                       (toMult'_slide rs_ahd' ts_ahd)

        _ ≡ `▷ r' `· `▷ t' `· toMult' (rs ++ ts) b
          := .multCong r_eq (.multCong t_eq (.refl rfl))

        _ ≡ (`▷ r' `· `▷ t') `· toMult' (rs ++ ts) b
          := .lahdMultAssoc

        _ ≡ (`▷ t' `· `▷ r') `· toMult' (rs ++ ts) b
          := .multCong lahd_mult_comm (.refl rfl)

        _ ≡ `▷ t' `· `▷ r' `· toMult' (rs ++ ts) b
          := .sym .lahdMultAssoc

        _ ≡ t `· r `· toMult' (rs ++ ts) b
          := .multCong (.sym t_eq) (.multCong (.sym r_eq) (.refl rfl))

        _ ≡ toMult' (t :: r :: rs ++ ts) b
          := .refl rfl


theorem toMult'_append_subset' {α} {b : RE α}{rs rs' : List (RE α)}
                               (rs_ahd  : ∀ x ∈ rs,  ∃ x', x ≡ `▷ x')
                               (sub : rs' ≡⊆ rs)
                               : toMult' (rs ++ rs') b ≡ toMult' rs b := by
  match rs' with
  | [] => simp
          exact .refl rfl
  | r :: rs' =>

      have r_in : r ≡∈ rs ++ rs' := by
        have ⟨r', eq, mem⟩ : r ≡∈ rs := sub List.mem_cons_self
        exact ⟨r', eq, List.mem_append_left rs' mem⟩

      have sub' : rs' ≡⊆ rs := by
        intro x x_in
        apply sub
        simp [x_in]

      have rs'_ahd : ∀ x ∈ r :: rs',  ∃ x', x ≡ `▷ x' := by
        intro x x_in
        have ⟨y, eq, mem⟩ := sub x_in
        have ⟨x', eq'⟩ := rs_ahd y mem
        exists x'
        exact .trans eq eq'

      have rs_rs'_ahd : ∀ x ∈ (rs ++ rs'),  ∃ x', x ≡ `▷ x' := by
        intro x x_in
        rcases List.mem_append.mp x_in with h | h
        . exact rs_ahd x h
        . exact rs'_ahd x (List.mem_cons.mpr (Or.inr h))

      calc toMult' (rs ++ r :: rs') b
        _ ≡ toMult' (r :: rs ++ rs') b := toMult'_slide rs_ahd rs'_ahd
        _ ≡ toMult' (rs ++ rs') b := toMult'_dup rs_rs'_ahd r_in
        _ ≡ toMult' rs b := toMult'_append_subset' rs_ahd sub'


theorem toMult'_base_eq {α} {rs : List (RE α)} {b b' : RE α}
                        (eq : b ≡ b')
                        : toMult' rs b ≡ toMult' rs b' := by
  match rs with
  | [] => simp [toMult']
          exact eq
  | r :: rs =>
      simp [toMult']
      exact .multCong (.refl rfl) (toMult'_base_eq eq)


theorem toMult'_mem_eq {α} {rs rs' : List (RE α)} {r r' : RE α}
                       (rs_ahd  : ∀ x ∈ rs,  ∃ x', x ≡ `▷ x')
                       (eqs : ∀ x, (x ≡∈ rs) ↔ x ≡∈ rs')
                       (eq : r ≡ r')
                       : toMult' rs r ≡ toMult' rs' r' := by
  have sub : rs ≡⊆ rs' := by
    intro x x_in
    apply (eqs x).mp
    exact ⟨x, .refl rfl, x_in⟩

  have sub' : rs' ≡⊆ rs := by
    intro x x_in
    apply (eqs x).mpr
    exact ⟨x, .refl rfl, x_in⟩

  have rs'_ahd : ∀ x ∈ rs', ∃ x', x ≡ `▷ x' := by
    intro x x_in
    have ⟨y, x_eq, y_in⟩ := sub' x_in
    have ⟨x', eq⟩ := rs_ahd y y_in
    exact ⟨x', .trans x_eq eq⟩

  calc toMult' rs r
    _ ≡ toMult' rs r'          := toMult'_base_eq eq
    _ ≡ toMult' (rs' ++ rs) r' := .sym (toMult'_append_subset rs_ahd sub')
    _ ≡ toMult' rs' r'         := toMult'_append_subset' rs'_ahd sub
