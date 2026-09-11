-- Our "words" are triples of lists

def Triple (α : Type) := List α × List α × List α

namespace Triple

def behind (t : Triple α) : List α :=
  let ⟨b, _, _⟩ := t
  b

def mtch (t : Triple α) : List α :=
  let ⟨_, m, _⟩ := t
  m

def ahead (t : Triple α) : List α :=
  let ⟨_, _, a⟩ := t
  a

theorem eta : ∀ (t : Triple α), t = (behind t, mtch t, ahead t) := by
  intro ⟨x, y, z⟩
  rfl

end Triple
