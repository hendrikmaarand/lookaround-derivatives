import LookaroundDerivatives.Triple

def Lang (α : Type) := Triple α → Prop


def LEq (k l : Lang α) :=
  ∀ t, k t ↔ l t


----------------------------------------------------------
-- Language constructors we consider

def symb (a : α) : Lang α := λ t =>
  mtch t = [a]

def empty : Lang α := λ _ => False

def top : Lang α := λ _ => True

def unit : Lang α := λ t =>
  mtch t = []

def union (k l : Lang α) : Lang α := λ t =>
  k t ∨ l t

def intersection (k l : Lang α) : Lang α := λ t =>
  k t ∧ l t

def diff (k l : Lang α) : Lang α := λ t =>
  k t ∧ ¬ l t

def concat (k l : Lang α) : Lang α := λ t =>
  ∃ (m₁ m₂ : List α),
    mtch t = m₁ ++ m₂ ∧
    k (behind t      , m₁, m₂ ++ ahead t) ∧
    l (behind t ++ m₁, m₂, ahead t)


-- Kleene star as inductive predicate.
-- TODO: step using concat explicitly?
inductive StarLFP (l : Lang α) : Lang α where
| base : {t : Triple α} → unit t → StarLFP l t
| step : {lb m₁ m₂ la m : List α} →
         m = m₁ ++ m₂ →
         l (lb, m₁, m₂ ++ la) →
         StarLFP l (lb ++ m₁, m₂, la) →
         StarLFP l (lb, m, la)

def kstar (l : Lang α) : Lang α := StarLFP l



def lookbehind (l : Lang α) : Lang α := λ t =>
  mtch t = [] ∧ l ([], behind t, ahead t)

def lookahead (l : Lang α) : Lang α := λ t =>
  mtch t = [] ∧ l (behind t, ahead t, [])

--------------------------------------------
-- notation

notation "∅" => empty

notation "𝕋" => top

notation "𝟙" => unit

prefix:max "$" => symb

infixr:55 " ∪ " => union

infixr:60 " ∩ " => intersection

infixl:55 " \\ " => diff

infixr:65 " ⊙ " => concat

postfix:max "⋆" => kstar

prefix:max "◁" => lookbehind

prefix:max "▷" => lookahead

infix:50 " ≐ " => LEq


----------------------------------------------
-- nullability and derivatives

def nlbl (l : Lang α) : Prop :=
  l ([], [], [])



def derLBhd (a : α) (l : Lang α) : Lang α := λ t =>
  l (a :: behind t, mtch t, ahead t)

def der (a : α) (l : Lang α) : Lang α := λ t =>
  behind t = [] ∧
  l ([], a :: mtch t, ahead t)

def derLAhd (a : α) (l : Lang α) : Lang α := λ t =>
  behind t = [] ∧ mtch t = [] ∧
  l ([], [], a :: ahead t)



def wderLBhd (w : List α) (l : Lang α) : Lang α :=
  match w with
  | []     => l
  | a :: w => wderLBhd w (derLBhd a l)

def wder (w : List α) (l : Lang α) : Lang α :=
  match w with
  | []     => l
  | a :: w => wder w (der a l)

def wderLAhd (w : List α) (l : Lang α) : Lang α :=
  match w with
  | [] => l
  | a :: w => wderLAhd w (derLAhd a l)



-- derivative wrt a triple
def tder (t : Triple α) (l : Lang α) : Lang α :=
  (wderLAhd (ahead t) ∘ wder (mtch t) ∘ wderLBhd (behind t)) l

-- "existential" derivative
def xder (a : α) (l : Lang α) : Lang α :=
  derLBhd a l ∪ der a l ∪ derLAhd a l

def wxder (w : List α) (l : Lang α) : Lang α :=
  match w with
  | []     => l
  | a :: w => wxder w (xder a l)

----------------------------------------------

theorem derLBhd_mem (a : α) (l : Lang α) (t : Triple α) :
    derLBhd a l t ↔ l (a :: behind t, mtch t, ahead t) := by
  rw [derLBhd]


theorem der_mem (a : α) (l : Lang α) : ∀ t, behind t = [] →
    (der a l t ↔ l (behind t, a :: mtch t, ahead t)) := by
  intro t t_eq
  rw [der, t_eq]
  simp

theorem der_mem' {α} : ∀ {a : α} {l : Lang α} {t : Triple α},
                 der a l t → behind t = [] := by
  intro a l t mem
  rw [der] at mem
  exact mem.1

theorem derLAhd_mem' {α} : ∀ {a : α} {l : Lang α} {t : Triple α},
                     derLAhd a l t → behind t = [] ∧ mtch t = [] := by
  intro a l t mem
  rw [derLAhd] at mem
  exact ⟨mem.1, mem.2.1⟩



theorem wderLBhd_mem (w : List α) (l : Lang α) :
    ∀ t, wderLBhd w l t ↔ l (w ++ behind t, mtch t, ahead t) := by
  intro t
  match w with
  | [] => rw [wderLBhd, List.nil_append]; rfl
  | a :: w => have ih := wderLBhd_mem w (derLBhd a l)
              rw [wderLBhd, ih, derLBhd]
              rfl

theorem wder_mem (w : List α) (l : Lang α) :
    ∀ t, behind t = [] → (wder w l t ↔ l (behind t, w ++ mtch t, ahead t)) := by
  intro t t_eq
  match w with
  | [] => rw [wder]; rw[List.nil_append]; rfl
  | a :: w => have ih := wder_mem w (der a l) t t_eq
              rw [wder, ih, der]
              rw [behind, mtch, ahead]
              apply Iff.intro
              . intro ⟨_, h⟩
                rw [t_eq]
                exact h
              . intro h
                apply And.intro t_eq
                rw [t_eq] at h
                exact h

theorem wderLAhd_mem (w : List α) (l : Lang α) :
    ∀ t, behind t = [] → mtch t = [] →
         (wderLAhd w l t ↔ l (behind t, mtch t, w ++ ahead t)) := by
  intro t bt mt
  match w with
  | [] => rw [wderLAhd]; rw[List.nil_append]; rfl
  | a :: w => have ih := wderLAhd_mem w (derLAhd a l) t bt mt
              rw [wderLAhd, ih, derLAhd]
              rw [behind, mtch, ahead]
              apply Iff.intro
              . intro ⟨_, _, h⟩
                rw [bt, mt]
                exact h
              . intro h
                rw [bt, mt] at h
                exact ⟨bt, mt, h⟩


-------------------------------------------------------------------

theorem nlbl_tder_iff_lang_mem (t : Triple α) (l : Lang α) :
    nlbl (tder t l) ↔ l t := by
  rw [tder, nlbl]
  rw [Function.comp_apply, Function.comp_apply]

  rw [wderLAhd_mem (ahead t) (wder (mtch t) (wderLBhd (behind t) l)) ([], [], []) rfl rfl]
  rw [behind, mtch, ahead, List.append_nil]

  rw [wder_mem (mtch t) (wderLBhd (behind t) l) ([], [], ahead t) rfl]
  rw [behind, mtch, ahead, List.append_nil]

  rw [wderLBhd_mem (behind t) l  ([], mtch t, ahead t)]
  rw [behind, mtch, ahead, List.append_nil]

  rfl

-------------------------------------------------------------------

theorem exists_mem_iff_wxder_nlbl (w : List α) (l : Lang α) :
    nlbl (wxder w l) ↔ ∃ (x y z : List α), w = x ++ y ++ z ∧ l (x, y, z) := by
  match w with
  | [] =>
      rw [wxder]
      apply Iff.intro
      . intro hn
        exists [], [], []
      . intro ⟨x, y, z, eq, mem⟩
        rw [nlbl]
        symm at eq
        rw [List.append_eq_nil_iff] at eq
        rw [List.append_eq_nil_iff] at eq
        rw [eq.1.1, eq.1.2, eq.2] at mem
        exact mem
  | a :: w =>
      rw [wxder, exists_mem_iff_wxder_nlbl w (xder a l), xder]
      simp [union, der, derLBhd, derLAhd, behind, mtch, ahead]

      apply Iff.intro
      . intro ⟨x, y, z, w_eq, p⟩
        apply Or.elim p
        . intro p
          exact ⟨a :: x, y, z, by simp [w_eq], p⟩
        . intro p
          apply Or.elim p
          . intro ⟨x_eq, p⟩
            exact ⟨[], a :: y, z, by simp [x_eq, w_eq], p⟩
          . intro ⟨x_eq, y_eq, p⟩
            exact ⟨[], [], a :: z, by simp [x_eq, y_eq, w_eq], p⟩

      . intro ⟨x, y, z, eq, p⟩
        apply Or.elim (List.cons_eq_append_iff.mp eq)
        . intro ⟨x_eq, eq⟩
          apply Or.elim (List.append_eq_cons_iff.mp eq)
          . intro ⟨y_eq, z_eq⟩
            rw [x_eq, y_eq, z_eq] at p
            exact ⟨[], [], w, rfl, Or.inr (Or.inr ⟨rfl, rfl, p⟩)⟩

          . intro ⟨y', y_eq, eq'⟩
            rw [x_eq, y_eq] at p
            exact ⟨[], y', z, eq', Or.inr (Or.inl ⟨rfl, p⟩)⟩

        . intro ⟨x', x_eq, eq'⟩
          rw [x_eq] at p
          exact ⟨x', y, z, eq', Or.inl p⟩




-----------------------------------------------------------------------
-- "prefix" lookaheads (the standard interpretation).
-- Match part of triple in l specifies a suffix/prefix
-- of a triple in lookbehind/lookahead.

def slb (l : Lang α) : Lang α := λ t =>
  mtch t = [] ∧
  ∃ x y, behind t = x ++ y ∧
         l (x, y, ahead t)

def pla (l : Lang α) : Lang α := λ t =>
  mtch t = [] ∧
  ∃ y z, ahead t = y ++ z ∧
         l (behind t, y, z)
