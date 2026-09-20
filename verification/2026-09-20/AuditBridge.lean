import Problem572.Main

namespace AuditBridge

open Finset

/-- Independent transcription of Frankl's eventual singleton-intersection theorem. -/
def IntendedStatement : Prop :=
  forall k : Nat, 4 <= k ->
    exists N : Nat, forall n : Nat, N <= n ->
      forall F : Finset (Finset (Fin n)),
        (forall A in F, A.card = k) ->
        Nat.choose (n - 2) (k - 2) < F.card ->
        exists A in F, exists B in F,
          A != B /\ (A intersect B).card = 1

theorem intended : IntendedStatement := by
  exact Problem572.erdos_sos_singleton_intersection

end AuditBridge
