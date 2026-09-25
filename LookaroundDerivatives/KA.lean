import LookaroundDerivatives.LangOpProperties

namespace Lang
open Triple

-- The operations of a Kleene algebra, without axioms.
structure KASig (A : Type) where
  plus : A → A → A
  mult : A → A → A
  star : A → A
  zero : A
  one  : A

-- The canonical order of an idempotent semiring, derived from `plus`.
def KASig.lt {A : Type} (S : KASig A) (a b : A) : Prop := S.plus a b = b

structure KA (A : Type) extends KASig A where
  plus_assoc : ∀ {a b c}, plus a (plus b c) = plus (plus a b) c
  plus_comm  : ∀ {a b}, plus a b = plus b a
  plus_idem  : ∀ {a}, plus a a = a
  plus_zero  : ∀ {a}, plus a zero = a

  mult_assoc : ∀ {a b c}, mult a (mult b c) = mult (mult a b) c
  mult_one_l : ∀ {a}, mult one a = a
  mult_one_r : ∀ {a}, mult a one = a
  mult_zero_l : ∀ {a}, mult zero a = zero
  mult_zero_r : ∀ {a}, mult a zero = zero

  distr_l : ∀ {a b c}, mult a (plus b c) = plus (mult a b) (mult a c)
  distr_r : ∀ {a b c}, mult (plus a b) c = plus (mult a c) (mult b c)

  star_pfp  : ∀ {a}, toKASig.lt (plus one (mult a (star a))) (star a)
  star_pfp' : ∀ {a}, toKASig.lt (plus one (mult (star a) a)) (star a)

  star_lfp  : ∀ {a b x}, toKASig.lt (plus b (mult a x)) x → toKASig.lt (mult (star a) b) x
  star_lfp' : ∀ {a b x}, toKASig.lt (plus b (mult x a)) x → toKASig.lt (mult b (star a)) x

-- Convenience so that `K.lt a b` works for `K : KA A`.
abbrev KA.lt {A : Type} (K : KA A) (a b : A) : Prop := K.toKASig.lt a b

theorem KA.lt_def {A : Type} (K : KA A) {a b : A} : K.lt a b ↔ K.plus a b = b := Iff.rfl


-------------------------------------------------------------------------

-- The language operators form a Kleene algebra.
def ka : KA (Lang α) :=
  { plus := union
  , mult := concat
  , star := kstar
  , zero := empty
  , one  := unit

  , plus_assoc := union_assoc
  , plus_comm  := union_comm
  , plus_idem  := union_idem
  , plus_zero  := union_identity_r

  , mult_assoc  := concat_assoc
  , mult_one_l  := concat_unit_l
  , mult_one_r  := concat_unit_r
  , mult_zero_l := concat_zero_l
  , mult_zero_r := concat_zero_r

  , distr_l := concat_distr_union_l
  , distr_r := concat_distr_union_r

  , star_pfp  := by intro a
                    exact subset_union_lemma.mp kstar_pfp
  , star_pfp' := by intro a
                    exact subset_union_lemma.mp kstar_pfp'
  , star_lfp  := by intro a b x eq
                    exact subset_union_lemma.mp (kstar_lfp (subset_union_lemma.mpr eq))
  , star_lfp' := by intro a b x eq
                    exact subset_union_lemma.mp (kstar_lfp' (subset_union_lemma.mpr eq)) }

end Lang
