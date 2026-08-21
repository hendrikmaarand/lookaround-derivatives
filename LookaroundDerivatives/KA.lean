import LookaroundDerivatives.LangOpProperties

structure KA (A : Type) where
  plus : A → A → A
  mult : A → A → A
  star : A → A
  zero : A
  one  : A

  lt (a b : A) := (plus a b) = b

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

  star_pfp  : ∀ {a}, lt (plus one (mult a (star a))) (star a)
  star_pfp' : ∀ {a}, lt (plus one (mult (star a) a)) (star a)

  star_lfp  : ∀ {a b x}, lt (plus b (mult a x)) x → lt (mult (star a) b) x
  star_lfp' : ∀ {a b x}, lt (plus b (mult x a)) x → lt (mult b (star a)) x


-------------------------------------------------------------------------

theorem LEq_ext_iff : ∀ {k l : Lang α}, k = l ↔ k ≐ l  := by
  intro k l
  apply Iff.intro
  . intro eq
    rw [eq]
    exact leq_refl
  . intro eq
    apply funext
    intro t
    rw [←iff_iff_eq]
    exact eq t

theorem LEq_ext : ∀ {k l : Lang α}, k ≐ l → k = l := by
  intro k l
  exact LEq_ext_iff.mpr


-- The language operators form a Kleene algebra.
def ka : KA (Lang α) :=
  { plus := union
  , mult := concat
  , star := kstar
  , zero := empty
  , one  := unit

  , lt a b := union a b = b

  , plus_assoc := LEq_ext union_assoc
  , plus_comm  := LEq_ext union_comm
  , plus_idem  := LEq_ext union_idem
  , plus_zero  := LEq_ext union_identity_r

  , mult_assoc  := LEq_ext concat_assoc
  , mult_one_l  := LEq_ext concat_unit_l
  , mult_one_r  := LEq_ext concat_unit_r
  , mult_zero_l := LEq_ext concat_zero_l
  , mult_zero_r := LEq_ext concat_zero_r

  , distr_l := LEq_ext concat_distr_union_l
  , distr_r := LEq_ext concat_distr_union_r

  , star_pfp  := by intro a
                    apply LEq_ext
                    intro t
                    rw [union, kstar_expand, union]
                    simp
  , star_pfp' := by intro a
                    apply LEq_ext
                    intro t
                    rw [union, kstar_expand', union]
                    simp
  , star_lfp  := by intro a b x eq
                    apply LEq_ext
                    rw [←subset_union_lemma]
                    rw [LEq_ext_iff, ←subset_union_lemma] at eq
                    intro t
                    apply kstar_lfp eq

  , star_lfp' := by intro a b x eq
                    apply LEq_ext
                    rw [←subset_union_lemma]
                    rw [LEq_ext_iff, ←subset_union_lemma] at eq
                    intro t
                    apply kstar_lfp' eq }
