
data Formula : Type where

  -- Ops
  Neg : Formula -> Formula
  Imp : Formula -> Formula -> Formula
  And : Formula -> Formula -> Formula



data T : Formula -> Type where 
  -- judgment
  -- for a formula phi, T phi is the set of proofs of phi  
  -- so, if M : T phi then M is a proof of phi

  -- M is a proof of phi <==> M : T (phi)
  
  -- Logics are represented in LF via a
  -- new principle, the judgements as types principle, whereby each judgement is identified with the type of
  -- its proofs.
  
  Ident : T p -> T p

  ImpI : (T p -> T q) -> T (p `Imp` q)
  ImpE : T (p `Imp` q) -> T p -> T q

  AndI : T p -> T q -> T (p `And` q)
  AndE1 : T (p `And` q) -> T p
  AndE2 : T (p `And` q) -> T q

  NegI : (T p -> T q) -> (T p -> T (Neg q)) -> T (Neg q)  
  NegE : T (Neg $ Neg p) -> T p





P, Q, R : Formula

proof1 : T (P `Imp` P)
proof1 = ImpI Ident


proof2 : T ((P `And` Q) `Imp` P)
proof2 = ImpI AndE1


proof3 : T ((P `And` Q) `Imp` Q)
proof3 = ImpI AndE2
