import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingCached
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.ForgeryClassify
/-!
# Canonical signed encoding targets

Every successful signer invocation using one one-time position computes the same layer message and
the same least admissible counter. Consequently an encoding collision at that position targets one
canonical signed payload, even when several signatures reuse the position.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def layerMessagePosition (index : Index) (lay : Layer) : Position :=
  if lay = topLayer then
    .node middleLayer (treeIndexAt index middleLayer)
      ⟨layerHeight middleLayer - 1, by decide⟩ ⟨0, by positivity⟩
  else if lay = middleLayer then
    .node middle2Layer (treeIndexAt index middle2Layer)
      ⟨layerHeight middle2Layer - 1, by decide⟩ ⟨0, by positivity⟩
  else if lay = middle2Layer then
    .node middle3Layer (treeIndexAt index middle3Layer)
      ⟨layerHeight middle3Layer - 1, by decide⟩ ⟨0, by positivity⟩
  else if lay = middle3Layer then
    .node bottomLayer (treeIndexAt index bottomLayer)
      ⟨layerHeight bottomLayer - 1, by decide⟩ ⟨0, by positivity⟩
  else .ftsRoots index

private theorem topLayer_ne_middleLayer : topLayer ≠ middleLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [topLayer, middleLayer] at this

private theorem middle2Layer_ne_topLayer : middle2Layer ≠ topLayer := by decide
private theorem middle2Layer_ne_middleLayer : middle2Layer ≠ middleLayer := by decide
private theorem middle3Layer_ne_topLayer : middle3Layer ≠ topLayer := by decide
private theorem middle3Layer_ne_middleLayer : middle3Layer ≠ middleLayer := by decide
private theorem middle3Layer_ne_middle2Layer : middle3Layer ≠ middle2Layer := by decide

private theorem bottomLayer_ne_topLayer : bottomLayer ≠ topLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [bottomLayer, topLayer, numLayers] at this

private theorem bottomLayer_ne_middleLayer : bottomLayer ≠ middleLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [bottomLayer, middleLayer, numLayers] at this

private theorem bottomLayer_ne_middle2Layer : bottomLayer ≠ middle2Layer := by decide
private theorem bottomLayer_ne_middle3Layer : bottomLayer ≠ middle3Layer := by decide

@[simp] theorem layerMessagePosition_top (index : Index) :
    layerMessagePosition index topLayer =
      .node middleLayer (treeIndexAt index middleLayer)
        ⟨layerHeight middleLayer - 1, by decide⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, if_pos rfl]

@[simp] theorem layerMessagePosition_middle (index : Index) :
    layerMessagePosition index middleLayer =
      .node middle2Layer (treeIndexAt index middle2Layer)
        ⟨layerHeight middle2Layer - 1, by decide⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, if_neg topLayer_ne_middleLayer.symm, if_pos rfl]

@[simp] theorem layerMessagePosition_middle2 (index : Index) :
    layerMessagePosition index middle2Layer =
      .node middle3Layer (treeIndexAt index middle3Layer)
        ⟨layerHeight middle3Layer - 1, by decide⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, if_neg middle2Layer_ne_topLayer,
    if_neg middle2Layer_ne_middleLayer, if_pos rfl]

@[simp] theorem layerMessagePosition_middle3 (index : Index) :
    layerMessagePosition index middle3Layer =
      .node bottomLayer (treeIndexAt index bottomLayer)
        ⟨layerHeight bottomLayer - 1, by decide⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, if_neg middle3Layer_ne_topLayer,
    if_neg middle3Layer_ne_middleLayer, if_neg middle3Layer_ne_middle2Layer, if_pos rfl]

@[simp] theorem layerMessagePosition_bottom (index : Index) :
    layerMessagePosition index bottomLayer = .ftsRoots index := by
  rw [layerMessagePosition, if_neg bottomLayer_ne_topLayer,
    if_neg bottomLayer_ne_middleLayer, if_neg bottomLayer_ne_middle2Layer,
    if_neg bottomLayer_ne_middle3Layer]

theorem eval_layerMessage_eq_honestValue (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (layerMessage secretKey index lay) =
      honestValue f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition index lay) := by
  have hlayer : lay = topLayer ∨ lay = middleLayer ∨ lay = middle2Layer ∨
      lay = middle3Layer ∨ lay = bottomLayer := by
    fin_cases lay
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext rfl))))
  rcases hlayer with rfl | rfl | rfl | rfl | rfl
  · rw [layerMessage_of_lt secretKey index topLayer (by decide)]
    rw [layerMessagePosition_top, honestValue_node]
    simp only [show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl]
    rfl
  · rw [layerMessage_of_lt secretKey index middleLayer (by decide)]
    rw [layerMessagePosition_middle, honestValue_node]
    simp only [show (⟨middleLayer.val + 1, by decide⟩ : Layer) = middle2Layer from rfl]
    rfl
  · rw [layerMessage_of_lt secretKey index middle2Layer (by decide)]
    rw [layerMessagePosition_middle2, honestValue_node]
    simp only [show (⟨middle2Layer.val + 1, by decide⟩ : Layer) = middle3Layer from rfl]
    rfl
  · rw [layerMessage_of_lt secretKey index middle3Layer (by decide)]
    rw [layerMessagePosition_middle3, honestValue_node]
    simp only [show (⟨middle3Layer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl]
    rfl
  · rw [layerMessage_bottomLayer secretKey index]
    rw [layerMessagePosition_bottom, honestValue_ftsRoots]
    rfl

end SphincsSecurity.Concrete
