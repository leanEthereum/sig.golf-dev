import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.LayerCompare
/-!
# Classifying an accepted forgery

Descent through the hypertree layers stops at a bad cache, at a one-time position not covered
exactly by the signing transcript, or at an honest few-time opening.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def VerifierLayerMessage (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (leaves : IndexGroup → FtsLeaf) (signature : Signature)
    (lay : Layer) (message : Digest) : Prop :=
  let ftsPublicKey := evalWithAnswerFn f
    (ftsRecover parameter index leaves signature.ftsSecret signature.ftsPath)
  ∃ bottomLeaf,
    evalWithAnswerFn f (otsLeafAttempt parameter bottomLayer (treeIndexAt index bottomLayer)
        (leafIndexAt index bottomLayer) ftsPublicKey (signature.counter bottomLayer)
        (signature.chainValue bottomLayer)) = some bottomLeaf
      ∧ let middle4Message := foldValue f parameter bottomLayer
          (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
        ∃ middle4Leaf,
          evalWithAnswerFn f (otsLeafAttempt parameter middle4Layer (treeIndexAt index middle4Layer)
              (leafIndexAt index middle4Layer) middle4Message (signature.counter middle4Layer)
              (signature.chainValue middle4Layer)) = some middle4Leaf
            ∧ let middle3Message := foldValue f parameter middle4Layer
                (treeIndexAt index middle4Layer) (leafIndexAt index middle4Layer)
                (signaturePath signature middle4Layer) middle4Leaf (layerHeight middle4Layer)
              ∃ middle3Leaf,
                evalWithAnswerFn f (otsLeafAttempt parameter middle3Layer (treeIndexAt index middle3Layer)
                    (leafIndexAt index middle3Layer) middle3Message (signature.counter middle3Layer)
                    (signature.chainValue middle3Layer)) = some middle3Leaf
                  ∧ let middle2Message := foldValue f parameter middle3Layer
                      (treeIndexAt index middle3Layer) (leafIndexAt index middle3Layer)
                      (signaturePath signature middle3Layer) middle3Leaf (layerHeight middle3Layer)
                    ∃ middle2Leaf,
                      evalWithAnswerFn f (otsLeafAttempt parameter middle2Layer (treeIndexAt index middle2Layer)
                          (leafIndexAt index middle2Layer) middle2Message (signature.counter middle2Layer)
                          (signature.chainValue middle2Layer)) = some middle2Leaf
                        ∧ let middleMessage := foldValue f parameter middle2Layer
                            (treeIndexAt index middle2Layer) (leafIndexAt index middle2Layer)
                            (signaturePath signature middle2Layer) middle2Leaf (layerHeight middle2Layer)
                          ∃ middleLeaf,
                            evalWithAnswerFn f (otsLeafAttempt parameter middleLayer (treeIndexAt index middleLayer)
                                (leafIndexAt index middleLayer) middleMessage (signature.counter middleLayer)
                                (signature.chainValue middleLayer)) = some middleLeaf
                              ∧ let topMessage := foldValue f parameter middleLayer
                                  (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
                                  (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
                                (lay = bottomLayer ∧ message = ftsPublicKey)
                                  ∨ (lay = middle4Layer ∧ message = middle4Message)
                                  ∨ (lay = middle3Layer ∧ message = middle3Message)
                                  ∨ (lay = middle2Layer ∧ message = middle2Message)
                                  ∨ (lay = middleLayer ∧ message = middleMessage)
                                  ∨ (lay = topLayer ∧ message = topMessage)

def FullyHonestOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (signature : Signature) : Prop :=
  (∀ lay, HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)
      ∧ CachedRun cache f (otsLeafAttempt secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay) (signature.chainValue lay)))
    ∧ (∀ tree,
      signature.ftsSecret tree = secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
        ∧ ∀ level (hlevel : level < ftsTreeHeight), signature.ftsPath tree ⟨level, hlevel⟩
          = honestFtsNode f secretKey.parameter index tree (secretKey.ftsSecret index tree) level
            (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1))
    ∧ CachedRun cache f
      (ftsRecover secretKey.parameter index leaves signature.ftsSecret signature.ftsPath)
    ∧ ∀ lay, VerifierLayerMessage f secretKey.parameter index leaves signature lay
      (evalWithAnswerFn f (layerMessage secretKey index lay))

theorem middleTree_eq_of_top_position_eq (leftIndex rightIndex : Index)
    (htree : treeIndexAt leftIndex topLayer = treeIndexAt rightIndex topLayer)
    (hleaf : leafIndexAt leftIndex topLayer = leafIndexAt rightIndex topLayer) :
    treeIndexAt leftIndex middleLayer = treeIndexAt rightIndex middleLayer := by
  apply Fin.ext
  rw [layers_link_top leftIndex, layers_link_top rightIndex, congrArg Fin.val htree,
    congrArg Fin.val hleaf]

theorem middle2Tree_eq_of_middle_position_eq (leftIndex rightIndex : Index)
    (htree : treeIndexAt leftIndex middleLayer = treeIndexAt rightIndex middleLayer)
    (hleaf : leafIndexAt leftIndex middleLayer = leafIndexAt rightIndex middleLayer) :
    treeIndexAt leftIndex middle2Layer = treeIndexAt rightIndex middle2Layer := by
  apply Fin.ext
  rw [layers_link_middle leftIndex, layers_link_middle rightIndex, congrArg Fin.val htree,
    congrArg Fin.val hleaf]

theorem middle3Tree_eq_of_middle2_position_eq (leftIndex rightIndex : Index)
    (htree : treeIndexAt leftIndex middle2Layer = treeIndexAt rightIndex middle2Layer)
    (hleaf : leafIndexAt leftIndex middle2Layer = leafIndexAt rightIndex middle2Layer) :
    treeIndexAt leftIndex middle3Layer = treeIndexAt rightIndex middle3Layer := by
  apply Fin.ext
  rw [layers_link_middle2 leftIndex, layers_link_middle2 rightIndex, congrArg Fin.val htree,
    congrArg Fin.val hleaf]

theorem middle4Tree_eq_of_middle3_position_eq (leftIndex rightIndex : Index)
    (htree : treeIndexAt leftIndex middle3Layer = treeIndexAt rightIndex middle3Layer)
    (hleaf : leafIndexAt leftIndex middle3Layer = leafIndexAt rightIndex middle3Layer) :
    treeIndexAt leftIndex middle4Layer = treeIndexAt rightIndex middle4Layer := by
  apply Fin.ext
  rw [layers_link_middle3 leftIndex, layers_link_middle3 rightIndex, congrArg Fin.val htree,
    congrArg Fin.val hleaf]

theorem bottomTree_eq_of_middle4_position_eq (leftIndex rightIndex : Index)
    (htree : treeIndexAt leftIndex middle4Layer = treeIndexAt rightIndex middle4Layer)
    (hleaf : leafIndexAt leftIndex middle4Layer = leafIndexAt rightIndex middle4Layer) :
    treeIndexAt leftIndex bottomLayer = treeIndexAt rightIndex bottomLayer := by
  apply Fin.ext
  rw [layers_link_middle4 leftIndex, layers_link_middle4 rightIndex, congrArg Fin.val htree,
    congrArg Fin.val hleaf]

theorem exact_top_message_eq_middle_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex topLayer = treeIndexAt forgedIndex topLayer)
    (hleaf : leafIndexAt signedIndex topLayer = leafIndexAt forgedIndex topLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex topLayer) = message) :
    message = honestNode f secretKey.parameter middleLayer
      (treeIndexAt forgedIndex middleLayer)
      (secretKey.otsSecret middleLayer (treeIndexAt forgedIndex middleLayer))
      (layerHeight middleLayer) 0 := by
  have hnext := middleTree_eq_of_top_position_eq signedIndex forgedIndex htree hleaf
  rw [← hmessage, layerMessage_of_lt secretKey signedIndex topLayer (by decide)]
  simp only [show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl, hnext]
  change evalWithAnswerFn f (treeNode secretKey.parameter middleLayer
    (treeIndexAt forgedIndex middleLayer)
    (secretKey.otsSecret middleLayer (treeIndexAt forgedIndex middleLayer))
    (layerHeight middleLayer) 0) = _
  rfl

theorem exact_middle_message_eq_middle2_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex middleLayer = treeIndexAt forgedIndex middleLayer)
    (hleaf : leafIndexAt signedIndex middleLayer = leafIndexAt forgedIndex middleLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex middleLayer) = message) :
    message = honestNode f secretKey.parameter middle2Layer
      (treeIndexAt forgedIndex middle2Layer)
      (secretKey.otsSecret middle2Layer (treeIndexAt forgedIndex middle2Layer))
      (layerHeight middle2Layer) 0 := by
  have hnext := middle2Tree_eq_of_middle_position_eq signedIndex forgedIndex htree hleaf
  rw [← hmessage, layerMessage_of_lt secretKey signedIndex middleLayer (by decide)]
  simp only [show (⟨middleLayer.val + 1, by decide⟩ : Layer) = middle2Layer from rfl, hnext]
  change evalWithAnswerFn f (treeNode secretKey.parameter middle2Layer
    (treeIndexAt forgedIndex middle2Layer)
    (secretKey.otsSecret middle2Layer (treeIndexAt forgedIndex middle2Layer))
    (layerHeight middle2Layer) 0) = _
  rfl

theorem exact_middle2_message_eq_middle3_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex middle2Layer = treeIndexAt forgedIndex middle2Layer)
    (hleaf : leafIndexAt signedIndex middle2Layer = leafIndexAt forgedIndex middle2Layer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex middle2Layer) = message) :
    message = honestNode f secretKey.parameter middle3Layer
      (treeIndexAt forgedIndex middle3Layer)
      (secretKey.otsSecret middle3Layer (treeIndexAt forgedIndex middle3Layer))
      (layerHeight middle3Layer) 0 := by
  have hnext := middle3Tree_eq_of_middle2_position_eq signedIndex forgedIndex htree hleaf
  rw [← hmessage, layerMessage_of_lt secretKey signedIndex middle2Layer (by decide)]
  simp only [show (⟨middle2Layer.val + 1, by decide⟩ : Layer) = middle3Layer from rfl, hnext]
  change evalWithAnswerFn f (treeNode secretKey.parameter middle3Layer
    (treeIndexAt forgedIndex middle3Layer)
    (secretKey.otsSecret middle3Layer (treeIndexAt forgedIndex middle3Layer))
    (layerHeight middle3Layer) 0) = _
  rfl

theorem exact_middle3_message_eq_middle4_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex middle3Layer = treeIndexAt forgedIndex middle3Layer)
    (hleaf : leafIndexAt signedIndex middle3Layer = leafIndexAt forgedIndex middle3Layer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex middle3Layer) = message) :
    message = honestNode f secretKey.parameter middle4Layer
      (treeIndexAt forgedIndex middle4Layer)
      (secretKey.otsSecret middle4Layer (treeIndexAt forgedIndex middle4Layer))
      (layerHeight middle4Layer) 0 := by
  have hnext := middle4Tree_eq_of_middle3_position_eq signedIndex forgedIndex htree hleaf
  rw [← hmessage, layerMessage_of_lt secretKey signedIndex middle3Layer (by decide)]
  simp only [show (⟨middle3Layer.val + 1, by decide⟩ : Layer) = middle4Layer from rfl, hnext]
  change evalWithAnswerFn f (treeNode secretKey.parameter middle4Layer
    (treeIndexAt forgedIndex middle4Layer)
    (secretKey.otsSecret middle4Layer (treeIndexAt forgedIndex middle4Layer))
    (layerHeight middle4Layer) 0) = _
  rfl

theorem exact_middle4_message_eq_bottom_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex middle4Layer = treeIndexAt forgedIndex middle4Layer)
    (hleaf : leafIndexAt signedIndex middle4Layer = leafIndexAt forgedIndex middle4Layer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex middle4Layer) = message) :
    message = honestNode f secretKey.parameter bottomLayer
      (treeIndexAt forgedIndex bottomLayer)
      (secretKey.otsSecret bottomLayer (treeIndexAt forgedIndex bottomLayer))
      (layerHeight bottomLayer) 0 := by
  have hnext := bottomTree_eq_of_middle4_position_eq signedIndex forgedIndex htree hleaf
  rw [← hmessage, layerMessage_of_lt secretKey signedIndex middle4Layer (by decide)]
  simp only [show (⟨middle4Layer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl, hnext]
  change evalWithAnswerFn f (treeNode secretKey.parameter bottomLayer
    (treeIndexAt forgedIndex bottomLayer)
    (secretKey.otsSecret bottomLayer (treeIndexAt forgedIndex bottomLayer))
    (layerHeight bottomLayer) 0) = _
  rfl

theorem exact_bottom_message_eq_fts_key (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex bottomLayer = treeIndexAt forgedIndex bottomLayer)
    (hleaf : leafIndexAt signedIndex bottomLayer = leafIndexAt forgedIndex bottomLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex bottomLayer) = message) :
    message = honestFtsKey f secretKey.parameter forgedIndex (secretKey.ftsSecret forgedIndex) := by
  have hindex := index_eq_of_bottom_position_eq htree hleaf
  subst signedIndex
  rw [← hmessage, layerMessage_bottomLayer]
  rfl

end SphincsSecurity.Concrete
