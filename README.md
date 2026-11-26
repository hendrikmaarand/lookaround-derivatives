# Derivatives of regular expressions with lookarounds

This repository is the Lean formalisation for the paper "Derivatives of regular expressions with lookarounds" by L. Gravier and H. Maarand ([https://doi.org/10.1007/978-981-92-8387-3_14](https://doi.org/10.1007/978-981-92-8387-3_14)).

# Structure

The development is organised in four namespaces:

- `Triple` (`Triple.lean`): the triples `(behind, match, ahead)` that play the role of words, with projections `Triple.behind`, `Triple.mtch`, `Triple.ahead`.
- `Lang` (`Language.lean`, `LangOpProperties.lean`, `LangDerProperties.lean`, `KA.lean`): languages of triples, the language operators and their semantic derivatives.
- `RE` (`Expressions.lean`, `DerProperties.lean`, `Correctness.lean`, `Shapes.lean`, `StarShapes.lean`, `ExistDerSum.lean`, `Finiteness.lean`): expressions, syntactic derivatives, the congruence `≡`, correctness with respect to `Lang`, and finiteness.
- `List` (`Lists.lean`): general list helpers (sublists, splits, ...) used by the finiteness argument.

# Paper-to-Lean mapping

Key definitions and results of the paper in `LookaroundDerivatives/`.

## Section 3: Languages

| Paper | Lean | File |
|---|---|---|
| Def. 1, nullability | `Lang.nlbl` | `Language.lean` |
| Def. 2, derivatives | `Lang.derLBhd`, `Lang.der`, `Lang.derLAhd` | `Language.lean` |
| Prop. 1 | `Lang.derLBhd_after_der` | `LangDerProperties.lean` |
| Def. 3, derivatives along a word | `Lang.wderLBhd`, `Lang.wder`, `Lang.wderLAhd` | `Language.lean` |
| Prop. 3, membership via derivatives | `Lang.nlbl_tder_iff_lang_mem` | `Language.lean` |
| Def. 4, existential derivative der♦ | `Lang.xder`, `Lang.wxder` | `Language.lean` |
| Prop. 4, existence of a match via der♦ | `Lang.exists_mem_iff_wxder_nlbl` | `Language.lean` |
| Def. 5, language operators| `Lang.concat`, `Lang.symb`, `Lang.union`, `Lang.kstar`, `Lang.lookbehind`, ... | `Language.lean` |
| Prop. 6, K ⊙ L = K ∩ L for K, L ⊆ 1 | `Lang.concat_subeps_inter` | `LangOpProperties.lean` |
| Props. 9–11, e.g. derₐ (K ⊙ L) | `Lang.der_concat` (also `Lang.derLBhd_kstar`, `Lang.derLAhd_lookahead`, ...) | `LangDerProperties.lean` |
| Def. 6, standard lookarounds slb, pla | `Lang.slb`, `Lang.pla` | `Language.lean` |
| Prop. 12, slb L = ◀(T ⊙ L), pla L = ▶(L ⊙ T) | `Lang.slb_from_lookbehind`, `Lang.pla_from_lookahead` | `LangOpProperties.lean` |

## Section 4: Expressions

| Paper | Lean | File |
|---|---|---|
| Def. 7, expressions RE | `RE` | `Expressions.lean` |
| Def. 8, semantics ⟦e⟧ | `RE.sem` | `Correctness.lean` |
| Def. 9, nullability N | `RE.N` | `Expressions.lean` |
| Prop. 13, N e ⟺ nlbl ⟦e⟧ | `RE.N_correct` | `Correctness.lean` |
| Def. 10, derivatives D◁, D, D▷ | `RE.DBhd`, `RE.D`, `RE.DAhd` | `Expressions.lean` |
| Prop. 14, e.g. ⟦Dₐ e⟧ = derₐ ⟦e⟧ | `RE.D_correct` | `Correctness.lean` |
| Def. 11, derivatives along a word | `RE.wDBhd`, `RE.wD`, `RE.wDAhd` | `Expressions.lean` |
| Thm. 1, membership via N and D | `RE.N_tD_iff_mem`, `RE.decideMem` | `Correctness.lean` |
| Def. 12, existential derivative D♢ | `RE.xD`, `RE.wxD` | `Expressions.lean` |
| Thm. 2, existence of a match via N and D♢ | `RE.N_wxD_iff_exists`, `RE.decideExists` | `Correctness.lean` |

## Section 5: Finiteness

| Paper | Lean | File |
|---|---|---|
| Def. 13, the congruence ≡ | `RE.Equiv` | `Expressions.lean` |
| Prop. 16, soundness of ≡ | `RE.equiv_sound` | `Correctness.lean` |
| Prop. 17, derivatives respect ≡ | `RE.DBhd_cong`, `RE.D_cong`, `RE.DAhd_cong` | `DerProperties.lean` |
| Prop. 18, e.g. Dᵦ (D▷ₐ e) ≡ 0 | `RE.D_after_DAhd_is_zero` | `DerProperties.lean` |
| Lemma 2, derivatives of e · f | `RE.wD_mult`, `RE.multShape` | `Shapes.lean` |
| Lemma 3, derivatives of e⋆ | `RE.wD_star_cons`, `RE.starShape`, `RE.starElem` | `StarShapes.lean` |
| Lemma 4, D▷ₐ e ≡ ▷ e′ | `RE.DAhd_exists`, `RE.extractLAhd` | `DerProperties.lean` |
| Prop. 19, ACI of multiplication on D▷ᵤ e | `RE.wDAhd_cons_mult_assoc`, `_comm`, `_idem` | `Shapes.lean` |
| Def. 14, successors e→ | `RE.succs` | `Finiteness.lean` |
| Prop. 21 / Thm. 3, every D▷_z (D_y (D◁_x e)) is ≡ to an element of e→ | `RE.wDAhd_wD_wDBhd_succs` | `Finiteness.lean` |
| Prop. 22, D♢ᵤ e as a sum of triple derivatives | `RE.wxD_equiv` | `ExistDerSum.lean` |
| Thm. 4, every D♢ᵤ e is ≡ to a sum over a subset of e→ | `RE.wxD_succs` | `Finiteness.lean` |
