 
-- Universe
Index : Type

data Formula : Type where
  -- Ops
  Neg : Formula -> Formula
  Imp : Formula -> Formula -> Formula
  And : Formula -> Formula -> Formula
  
  Equal : Index -> Index -> Formula
  Forall : (Index -> Formula) -> Formula
  Exists : (Index -> Formula) -> Formula

-- if ε(∃ϕ) = t then (ϕ t)
Choice : (Index -> Formula) -> Index

-- propositions as types
-- proofs as terms


-- "Logics are represented in LF via a new principle, 
-- the judgements as types principle, whereby each judgement is identified with the type of its proofs."

data T : Formula -> Type where 
  -- judgment
  -- for a formula phi, T phi is the set of proofs of phi  
  -- so, if M : T phi then M is a proof of phi

  -- M is a proof of phi <==> M : T (phi)
  
  -- Logics are represented in LF via a
  -- new principle, the judgements as types principle, whereby each judgement is identified with the type of
  -- its proofs.
  
  Ident : T phi -> T phi

  ImpI : (T phi -> T psi) -> T (phi `Imp` psi)
  ImpE : T (phi `Imp` psi) -> T psi -> T phi

  AndI : T phi -> T psi -> T (phi `And` psi)
  AndE1 : T (phi `And` psi) -> T phi
  AndE2 : T (phi `And` psi) -> T psi

  NegI : (T phi -> T psi) -> (T phi -> T (Neg psi)) -> T (Neg psi)  
  NegE : T (Neg $ Neg psi) -> T psi

  Equal0 : {x : Index} -> T (x `Equal` x) 
  Equal1 : {term : Index-> Index} -> T (x `Equal` y) -> T ((term x) `Equal` (term y))
  Equal2 : {phi : Index -> Formula} -> T (x `Equal` y) -> T (phi x) -> T (phi y)
  
  ChoiceI : {phi : Index -> Formula} -> T (Exists phi) -> T (phi (Choice phi))  
  
  ExistsE : {phi : Index -> Formula} -> {psi : Formula}  -> T (Exists phi) -> (T (Exists phi) -> T psi) -> T psi
  ExistsI : {phi : Index -> Formula} -> {t : Index} -> T (phi t) -> T (Exists phi)   
  
  ForallE : {phi : Index -> Formula} -> {t : Index} -> T (Forall phi) -> T (phi t)
  ForallI : {phi : Index -> Formula} -> {t : Index} -> T (phi t) -> T (Forall phi)




--  ∀x.Φ ⊢ ∃x.Φ
lemma : {phi : Index -> Formula} -> T (Forall phi) -> T (Exists phi)
lemma p = ExistsI $ ForallE {phi} {t} p
  where
    t : Index
    t = Choice phi

--  ∀x.Φ → ∃x.Φ
proofFOL : {phi : Index -> Formula} -> T ((Forall phi) `Imp` (Exists phi))
proofFOL = ImpI lemma

P, Q, R : Formula

-- P → P
proof1 : T (P `Imp` P)
proof1 = ImpI Ident

-- (P ∧ Q) → P
proof2 : T ((P `And` Q) `Imp` P)
proof2 = ImpI AndE1

-- (P ∧ Q) → Q
proof3 : T ((P `And` Q) `Imp` Q)
proof3 = ImpI AndE2

-- ∀ x . x = x
proof4 : T ( Forall (\x : Index => x `Equal` x) )
proof4 = ForallI (Equal0 {x})
  where x : Index


 --  ∀x.Φ → ∃x.Φ
foo1 : {x : Type} -> {P : Type -> Type} -> ( (x) -> P x ) -> (x ** P x)
foo1 f = (x ** (f y))
  where y : x
        
-- ∀ x . x = x 
foo : (x: Type) -> x = x
foo x = Refl


