
namespace Ind
open Timed

-- the environment's step of the composed system keeps the invariant
theorem inv_env (T T' : TSys) (h : Inv T) (e : Relay.Ev) (he : tDoEnv T e = some T') : Inv T' := by
  cases e with
  | connect _ => simp [tDoEnv] at he
  | deny _ => simp [tDoEnv] at he
  | send _ _ => simp [tDoEnv] at he
  | discard _ => simp [tDoEnv] at he
  | read _ _ => simp [tDoEnv] at he
  | close _ => simp [tDoEnv] at he
  | sock id g kk =>
    unfold tDoEnv at he
    dsimp only at he
    by_cases hA : (!Client.envAllowed T.c id g kk) = true
    · rw [if_pos hA] at he
      cases he
    · rw [if_neg hA] at he
      have hT := Option.some.inj he
      subst hT
      exact inv_sock T _ h id g kk rfl rfl rfl rfl rfl rfl

end Ind
