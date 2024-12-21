(* Formalization of the *decisional* MLWE problem. *)
(* That is, distinguishing between (A, A x + e) and (A, t) for random t. *)

require import AllCore Distr IntDiv.
require (*--*) DynMatrix.

(* Mat alreary requires that the underlying carrier is a ComRing *)
clone import DynMatrix as M.

op k : { int | 0 < k } as gt0_k.
op l : { int | 0 < l } as gt0_l.

(* The uniform distribution over the elements of the ring *)
op dR : R distr.
axiom dR_ll : is_lossless dR.
axiom dR_funi : is_funiform dR.

(* The error distribution *)
op chi : vector distr = dvector dR k.
lemma chi_ll : is_lossless chi.
  smt(@M dR_ll).
qed.
  
lemma chi_k x : x \in chi => size x = k.
  smt(@M gt0_k).
qed.
  
module type Adversary = {
  proc distinguish(mA: matrix, t: vector) : bool
}.

module GameL(A: Adversary) = {
  proc main() = {
    var mA, x, e, result;
    mA <$ dmatrix dR k l;
    x <$ dvector dR l;
    e <$ chi;
    result <@ A.distinguish(mA, mA *^ x + e);
    return result;
  }
}.

module GameR(A: Adversary) = {
  proc main() = {
    var mA, r, result;
    mA <$ dmatrix dR k l;
    r <$ dvector dR k;
    result <@ A.distinguish(mA, r);
    return result;
  }
}.

    (* Note that in ZKPT12_aux we restrict the chi and R
    such that this becomes the exact learing parity with noise problem *)
