import LookaroundDerivatives.Triple
import LookaroundDerivatives.Expressions
import LookaroundDerivatives.Lists
import LookaroundDerivatives.DerProperties
import LookaroundDerivatives.Shapes


theorem toSum_map_zero {X} {α} [DecidableEq α]
                       (xs : List X)
                       : toSum (List.map (λ _ => `0) xs) ≡ (`0 : RE α) := by
  match xs with
  | [] => simp [toSum]
          exact .refl rfl
  | x :: xs =>
      simp [toSum]
      apply Equiv.trans .plusZeroL
      apply toSum_map_zero


def trpls' (u : List α) (t : Triple α) : List (Triple α) :=
  match u with
  | [] => [t]
  | a :: u =>
      match t with
      | (x, [], []) => trpls' u (x ++ [a], [], []) ++
                       trpls' u (x, [a], []) ++
                       trpls' u (x, [], [a])
      | (x, y, [])  => trpls' u (x, y ++ [a], []) ++
                       trpls' u (x, y, [a])
      | (x, y, z)   => trpls' u (x, y, z ++ [a])


-- all factorisations of u as a triple.
def trpls (u : List α) : List (Triple α) :=
  trpls' u ([], [], [])

#eval trpls' ([] : List Nat) ([], [], [])

theorem trpls'_ne : ∀ (u x y z : List α), trpls' u (x, y, z) ≠ [] := by
  intro u x y z
  match u with
  | [] => simp [trpls']
  | a :: u =>
      match z with
      | [] =>
          match y with
          | [] => simp [trpls', trpls'_ne]
          | b :: y => simp [trpls', trpls'_ne]
      | c :: z => simp [trpls', trpls'_ne]

theorem trpls_ne : ∀ (u : List α), trpls u ≠ [] := by
  intro u
  simp [trpls, trpls'_ne]


theorem trpls'_x : (x, y, z) ∈ trpls' u (x' ++ [a], [], []) →
                   (x, y, z) ∈ trpls' (a :: u) (x', [], []) := by
  intro mem
  simp [trpls']
  simp [mem]

theorem trpls'_y : (x, y, z) ∈ trpls' u (x', y' ++ [a], []) →
                   (x, y, z) ∈ trpls' (a :: u) (x', y', []) := by
  intro mem
  match y' with
      | [] =>
          simp [trpls']
          simp at mem
          simp [mem]
      | b' :: y' =>
          simp [trpls']
          simp at mem
          simp [mem]


theorem trpls'_z : (x, y, z) ∈ trpls' u (x', y', z' ++ [a]) →
                   (x, y, z) ∈ trpls' (a :: u) (x', y', z') := by
  intro mem
  match z' with
  | [] =>
      match y' with
      | [] =>
          simp [trpls']
          simp at mem
          simp [mem]
      | b' :: y' =>
          simp [trpls']
          simp at mem
          simp [mem]
  | c' :: z' =>
      simp [trpls']
      simp at mem
      exact mem


theorem trpls_sound' {α} : ∀ (u : List α) {x y z x' y' z' : List α},
                            (x, y, z) ∈ trpls' u (x', y', z') →
                            x ++ y ++ z = x' ++ y' ++ z' ++ u := by
  intro u x y z x' y' z' mem
  match u with
  | [] => simp_all [trpls']
  | a :: u =>
      match z' with
      | [] =>
          match y' with
          | [] => simp [trpls'] at mem
                  rcases mem with h | h | h <;>
                  simp [trpls_sound' u h]

          | b' :: y' =>
              simp [trpls'] at mem
              rcases mem with h | h <;>
              simp [trpls_sound' u h]
      | c' :: z' =>
          simp [trpls'] at mem
          have ih := trpls_sound' u mem
          simp [ih]

theorem trpls_sound : ∀ (u : List α) {x y z : List α},
                            (x, y, z) ∈ trpls u →
                            x ++ y ++ z = u := by
  intro u x y z mem
  rw [trpls] at mem
  simp [trpls_sound' u mem]


theorem trpls'_complete {α} : ∀ {x y z t : List α} (u : List α),
                                x ++ y ++ z = t ++ u →
                                ∃ x' y' z', t = x' ++ y' ++ z' ∧
                                  (x, y, z) ∈ trpls' u (x', y', z') := by
  intro x y z t u eq
  match u with
  | [] => simp [trpls'] at *
          exists x, y, z
          simp [eq]
  | a :: u =>
      have eq' : x ++ y ++ z = t ++ [a] ++ u := by simp [eq]
      have ⟨x', y', z', t_eq, mem⟩ := trpls'_complete u eq'

      rw [List.append_eq_append_iff] at t_eq
      apply Or.elim t_eq
      . intro ⟨as, p, q⟩
        symm at q
        rw [List.append_eq_singleton_iff] at q
        rcases q with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        . subst h₁ h₂
          exists x', y', []
          simp [p]
          exact trpls'_z mem
        . subst h₁ h₂
          rw [List.append_eq_append_iff] at p
          rcases p with ⟨as, h₁, h₂⟩ | ⟨bs, h₁, h₂⟩
          . exists x', as, []
            simp [h₁]
            rw [h₂] at mem
            exact trpls'_y mem

          . symm at h₂
            rw [List.append_eq_singleton_iff] at h₂
            rcases h₂ with ⟨g₁, g₂⟩ | ⟨g₁, g₂⟩
            . subst g₁
              exists x', [], []
              simp at h₁
              simp [←h₁]
              rw [g₂] at mem
              exact trpls'_y mem

            . subst g₁ g₂
              exists t, [], []
              simp
              rw [h₁] at mem
              exact trpls'_x mem

      . intro ⟨bs, p, q⟩
        exists x', y', bs
        simp [p]
        rw [q] at mem
        exact trpls'_z mem


theorem trpls_complete {α} : ∀ {x y z : List α} (u : List α),
                               x ++ y ++ z = u →
                              (x, y, z) ∈ trpls u := by
  intro x y z u eq
  rw [trpls]
  have eq' : x ++ y ++ z = [] ++ u := by simp [eq]
  have ⟨x', y', z', eq, mem⟩  := trpls'_complete u eq'
  simp at eq
  simp [eq] at mem
  exact mem


theorem trpls_cons_bhd (u : List α) (a : α)
                   : trpls' u (a :: x, y, z)
                     = List.map (λ (x', y', z') => (a :: x', y', z'))
                                (trpls' u (x, y, z)) := by
  match u with
  | [] => rfl
  | b :: u =>
      match z with
      | [] =>
          match y with
          | [] => simp [trpls', trpls_cons_bhd]
          | c' :: y => simp [trpls', trpls_cons_bhd]
      | c' :: z =>
          simp [trpls', trpls_cons_bhd]


theorem tD_cong {α} [DecidableEq α]  {t : Triple α} {e f : RE α}
                     (eq : e ≡ f)
                     : tD t e ≡ tD t f := by
  rw [tD, tD]
  apply wDAhd_cong
  apply wD_cong
  apply wDBhd_cong
  exact eq

theorem tD_zero {α} [DecidableEq α]  {t : Triple α} {e : RE α}
                     (eq : e ≡ `0)
                     : tD t e ≡ `0 := by
  apply Equiv.trans (tD_cong eq)
  apply Equiv.trans (wDAhd_cong (wD_cong (by apply wDBhd_0)))
  apply Equiv.trans (wDAhd_cong (by apply wD_0))
  apply Equiv.trans (by apply wDAhd_0)
  exact .refl rfl



theorem tD_DBhd {α} [DecidableEq α] (e : RE α) (a : α) (u x y z: List α)
                     : List.map (flip tD e) (trpls' u (a :: x, y, z))
                       =
                       List.map (flip tD (DBhd a e)) (trpls' u (x, y, z)) := by
  rw [trpls_cons_bhd]
  rw [List.map_map]
  rfl


theorem tD_DBhd_after_D_zero {α} [DecidableEq α] (e : RE α) (a b : α) (u x y z : List α)
                            : toSum (List.map (flip tD (D a e)) (trpls' u (b :: x, y, z))) ≡ `0 := by
  rw [tD_DBhd]
  calc toSum (List.map (flip tD (DBhd b (D a e))) (trpls' u (x, y, z)))
    _ ≡ toSum (List.map (λ _ => `0) (trpls' u (x, y, z)))
      := by apply toSum_map
            intro t t_in
            apply tD_zero
            apply DBhd_after_D_is_zero
    _ ≡ `0
      := toSum_map_zero (trpls' u (x, y, z))

theorem tD_DBhd_after_DAhd_zero {α} [DecidableEq α] (e : RE α) (a b : α) (u x y z : List α)
                                : toSum (List.map (flip tD (DAhd a e)) (trpls' u (b :: x, y, z))) ≡ `0 := by
  rw [tD_DBhd]
  calc toSum (List.map (flip tD (DBhd b (DAhd a e))) (trpls' u (x, y, z)))
    _ ≡ toSum (List.map (λ _ => `0) (trpls' u (x, y, z)))
      := by apply toSum_map
            intro t t_in
            apply tD_zero
            apply DBhd_after_DAhd_is_zero
    _ ≡ `0
      := toSum_map_zero (trpls' u (x, y, z))


theorem tD_D {α} [DecidableEq α] (e : RE α) (a : α) (u y z: List α)
                     : toSum (List.map (flip tD e) (trpls' u ([], a :: y, z)))
                       ≡
                       toSum (List.map (flip tD (D a e)) (trpls' u ([], y, z))) := by
  match u with
  | [] => simp [trpls']
          exact .refl rfl
  | b :: u =>
      match z with
      | [] =>
          simp [trpls']
          match y with
          | [] =>
              simp only [List.nil_append, List.map_append]
              calc toSum (List.map (flip tD e) (trpls' u ([], [a, b], []))
                          ++ List.map (flip tD e) (trpls' u ([], [a], [b])))
                _ ≡ toSum (List.map (flip tD e) (trpls' u ([], [a, b], [])))
                    `+ toSum (List.map (flip tD e) (trpls' u ([], [a], [b])))
                  := toSum_append
                _ ≡ toSum (List.map (flip tD (D a e)) (trpls' u ([], [b], [])))
                    `+ toSum (List.map (flip tD (D a e)) (trpls' u ([], [], [b])))
                  := .plusCong (by apply tD_D) (by apply tD_D)
                _ ≡ `0
                    `+ toSum (List.map (flip tD (D a e)) (trpls' u ([], [b], [])))
                    `+ toSum (List.map (flip tD (D a e)) (trpls' u ([], [], [b])))
                  := .sym .plusZeroL
                _ ≡ toSum (List.map (flip tD (D a e)) (trpls' u ([b], [], [])))
                    `+ toSum (List.map (flip tD (D a e)) (trpls' u ([], [b], [])))
                    `+ toSum (List.map (flip tD (D a e)) (trpls' u ([], [], [b])))
                  := .plusCong (Equiv.sym (by apply tD_DBhd_after_D_zero))
                               (.refl rfl)
                _ ≡ toSum (List.map (flip tD (D a e)) (trpls' u ([b], [], []))
                           ++ (List.map (flip tD (D a e)) (trpls' u ([], [b], []))
                           ++ List.map (flip tD (D a e)) (trpls' u ([], [], [b]))))
                  := Equiv.trans (.plusCong (.refl rfl)
                                            (.sym toSum_append))
                                 (.sym toSum_append)
          | c :: y =>
              simp
              apply Equiv.trans toSum_append
              apply Equiv.trans (Equiv.plusCong (by apply tD_D) (by apply tD_D))
              apply Equiv.sym toSum_append

      | c :: z =>
          simp [trpls']
          apply tD_D



theorem tD_D_after_DAhd_zero {α} [DecidableEq α] (e : RE α) (a b : α) (u y z : List α)
                             : toSum (List.map (flip tD (DAhd a e)) (trpls' u ([], b :: y, z))) ≡ `0 := by
  calc toSum (List.map (flip tD (DAhd a e)) (trpls' u ([], b :: y, z)))
    _ ≡ toSum (List.map (flip tD (D b (DAhd a e))) (trpls' u ([], y, z)))
      := by apply tD_D
    _ ≡ toSum (List.map (λ _ => `0) (trpls' u ([], y, z)))
      := by apply toSum_map
            intro t t_in
            apply tD_zero
            apply D_after_DAhd_is_zero
    _ ≡ `0
      := toSum_map_zero (trpls' u ([], y, z))





theorem tD_DAhd {α} [DecidableEq α] (e : RE α) (a : α) (u z: List α)
                      : toSum (List.map (flip tD e) (trpls' u ([], [], a :: z)))
                        ≡
                        toSum (List.map (flip tD (DAhd a e)) (trpls' u ([], [], z))) := by
  match u with
  | [] => simp [trpls']
          exact .refl rfl
  | b :: u =>
      match z with
      | [] => simp [trpls']
              calc toSum (List.map (flip tD e) (trpls' u ([], [], [a, b])))
                _ ≡ toSum (List.map (flip tD (DAhd a e)) (trpls' u ([], [], [b])))
                  := by apply tD_DAhd
                _ ≡ `0 `+ toSum (List.map (flip tD (DAhd a e)) (trpls' u ([], [], [b])))
                  := .sym .plusZeroL
                _ ≡ `0 `+ `0 `+ toSum (List.map (flip tD (DAhd a e)) (trpls' u ([], [], [b])))
                  := .sym .plusZeroL

                _ ≡ toSum (List.map (flip tD (DAhd a e)) (trpls' u ([b], [], [])))
                    `+ toSum (List.map (flip tD (DAhd a e)) (trpls' u ([], [b], [])))
                    `+ toSum (List.map (flip tD (DAhd a e)) (trpls' u ([], [], [b])))
                  := .plusCong (Equiv.sym (by apply tD_DBhd_after_DAhd_zero))
                               (.plusCong (Equiv.sym (by apply tD_D_after_DAhd_zero))
                                          (.refl rfl))

                _ ≡ toSum (List.map (flip tD (DAhd a e)) (trpls' u ([b], [], []))
                           ++ (List.map (flip tD (DAhd a e)) (trpls' u ([], [b], []))
                           ++ List.map (flip tD (DAhd a e)) (trpls' u ([], [], [b]))))
                  := Equiv.trans (.plusCong (.refl rfl)
                                            (.sym toSum_append))
                                 (.sym toSum_append)
      | c :: z =>
          simp [trpls']
          apply tD_DAhd




-- existential derivative of e along a word u is equivalent to a sum
-- of all triple-derivatives over all factorisations of u as a triple.
theorem wxD_equiv {α} [DecidableEq α]
                  : ∀ (u : List α) (e : RE α),
                      wxD u e ≡ toSum (List.map (flip tD e)
                                                (trpls u)) := by
  intro u e
  match u with
  | [] => simp [wxD]
          exact .sym (plus_zero_r)

  | a :: u =>
      calc wxD (a :: u) e
        _ ≡ wxD u (DBhd a e `+ D a e `+ DAhd a e)
          := .refl rfl
        _ ≡ wxD u (DBhd a e) `+ wxD u (D a e `+ DAhd a e)
          := by apply wxD_plus
        _ ≡ wxD u (DBhd a e) `+ wxD u (D a e) `+ wxD u (DAhd a e)
          := .plusCong (.refl rfl) (by apply wxD_plus)
        _ ≡ (wxD u (DBhd a e) `+ wxD u (D a e)) `+ wxD u (DAhd a e)
          := .plusAssoc
        _ ≡ (toSum (List.map (flip tD (DBhd a e)) (trpls' u ([], [], [])))
            `+ toSum (List.map (flip tD (D a e)) (trpls' u ([], [], []))))
            `+ toSum (List.map (flip tD (DAhd a e)) (trpls' u ([], [], [])))
          := .plusCong (.plusCong (by apply wxD_equiv)
                                  (by apply wxD_equiv))
                       (by apply wxD_equiv)

        _ ≡ (toSum (List.map (flip tD e) (trpls' u ([a], [], [])))
            `+ toSum (List.map (flip tD e) (trpls' u ([], [a], []))))
            `+ toSum (List.map (flip tD e) (trpls' u ([], [], [a])))
          := .plusCong (.plusCong (.refl (by rw [tD_DBhd]))
                                  (.sym (by apply tD_D)))
                       (.sym (by apply tD_DAhd))
        _ ≡ toSum (List.map (flip tD e) (trpls' u ([a], [], []))
                   ++ List.map (flip tD e) (trpls' u ([], [a], [])))
            `+ toSum (List.map (flip tD e) (trpls' u ([], [], [a])))
          := .plusCong (.sym toSum_append) (.refl rfl)
        _ ≡ toSum (List.map (flip tD e) (trpls' u ([a], [], []))
                   ++ List.map (flip tD e) (trpls' u ([], [a], []))
                   ++ List.map (flip tD e) (trpls' u ([], [], [a])))
          := .sym toSum_append
        _ ≡ toSum (List.map (flip tD e) (trpls' u ([a], [], [])
                                          ++ trpls' u ([], [a], [])
                                          ++ trpls' u ([], [], [a])))
          := .refl (by simp)
        _ ≡ toSum (List.map (flip tD e) (trpls' (a :: u) ([], [], [])))
          := .refl rfl
        _ ≡ toSum (List.map (flip tD e) (trpls (a :: u)))
          := .refl rfl
