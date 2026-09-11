# lookaround-derivatives
Lean formalisation of the paper "Derivatives of regular expressions with lookarounds".

# Paper-to-Lean mapping

Key definitions and results of the paper in `LookaroundDerivatives/`.

## Section 3: Languages

| Paper | Lean | File |
|---|---|---|
| Def. 1, nullability | `nlbl` | `Language.lean` |
| Def. 2, derivatives | `derLBhd`, `der`, `derLAhd` | `Language.lean` |
| Prop. 1 | `derLBhd_after_der` | `LangDerProperties.lean` |
| Def. 3, derivatives along a word | `wderLBhd`, `wder`, `wderLAhd` | `Language.lean` |
| Prop. 2, e.g. der_{uv} L = der_v (der_u L) | `wder_append` (also `wderLBhd_append`, `wderLAhd_append`) | `Language.lean` |
| Prop. 3, membership via derivatives | `nlbl_tder_iff_lang_mem` | `Language.lean` |
| Def. 4, existential derivative der♦ | `xder`, `wxder` | `Language.lean` |
| Prop. 4, existence of a match via der♦ | `exists_mem_iff_wxder_nlbl` | `Language.lean` |
| Def. 5, language operators| `concat`, `symb`, `union`, `kstar`, `lookbehind`, ... | `Language.lean` |
| Prop. 6, K ⊙ L = K ∩ L for K, L ⊆ 1 | `concat_subeps_inter` | `LangOpProperties.lean` |
| Props. 9–11, e.g. derₐ (K ⊙ L) | `der_concat` (also `derLBhd_kstar`, `derLAhd_lookahead`, ...) | `LangDerProperties.lean` |
| Def. 6, standard lookarounds slb, pla | `slb`, `pla` | `Language.lean` |
| Prop. 12, slb L = ◀(T ⊙ L), pla L = ▶(L ⊙ T) | `slb_from_lookbehind`, `pla_from_lookahead` | `LangOpProperties.lean` |

## Section 4: Expressions

| Paper | Lean | File |
|---|---|---|
| Def. 7, expressions RE | `RE` | `Expressions.lean` |
| Def. 8, semantics ⟦e⟧ | `sem` | `Correctness.lean` |
| Def. 9, nullability N | `N` | `Expressions.lean` |
| Prop. 13, N e ⟺ nlbl ⟦e⟧ | `N_correct` | `Correctness.lean` |
| Def. 10, derivatives D◁, D, D▷ | `DBhd`, `D`, `DAhd` | `Expressions.lean` |
| Prop. 14, e.g. ⟦Dₐ e⟧ = derₐ ⟦e⟧ | `D_correct` | `Correctness.lean` |
| Def. 11, derivatives along a word | `wDBhd`, `wD`, `wDAhd` | `Expressions.lean` |
| Thm. 1, membership via N and D | `N_tD_iff_mem`, `decideMem` | `Correctness.lean` |
| Def. 12, existential derivative D♢ | `xD`, `wxD` | `Expressions.lean` |
| Thm. 2, existence of a match via N and D♢ | `N_wxD_iff_exists`, `decideExists` | `Correctness.lean` |

## Section 5: Finiteness

| Paper | Lean | File |
|---|---|---|
| Def. 13, the congruence ≡ | `Equiv` | `Expressions.lean` |
| Prop. 16, soundness of ≡ | `equiv_sound` | `Correctness.lean` |
| Prop. 17, derivatives respect ≡ | `DBhd_cong`, `D_cong`, `DAhd_cong` | `DerProperties.lean` |
| Prop. 18, e.g. Dᵦ (D▷ₐ e) ≡ 0 | `D_after_DAhd_is_zero` | `DerProperties.lean` |
| Lemma 2, derivatives of e · f | `wD_mult`, `multShape` | `Shapes.lean` |
| Lemma 3, derivatives of e⋆ | `wD_star_cons`, `starShape`, `starElem` | `StarShapes.lean` |
| Lemma 4, D▷ₐ e ≡ ▷ e′ | `DAhd_exists`, `extractLAhd` | `DerProperties.lean` |
| Prop. 19, ACI of multiplication on D▷ᵤ e | `wDAhd_cons_mult_assoc`, `_comm`, `_idem` | `Shapes.lean` |
| Def. 14, successors e→ | `succs` | `Finiteness.lean` |
| Prop. 21 / Thm. 3, every D▷_z (D_y (D◁_x e)) is ≡ to an element of e→ | `wDAhd_wD_wDBhd_succs` | `Finiteness.lean` |
| Prop. 22, D♢ᵤ e as a sum of triple derivatives | `wxD_equiv` | `ExistDerSum.lean` |
| Thm. 4, every D♢ᵤ e is ≡ to a sum over a subset of e→ | `wxD_succs` | `Finiteness.lean` |
