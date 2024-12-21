require import AllCore Distr DInterval  IntDiv List Perms.

require (*--*) Commitment.

require (*--*) SigmaProtocol3.
require (*--*) MLWE.

import MLWE.
import M.

require JKPT12_aux.
import JKPT12_aux.
export JKPT12_aux.

(* Instantiate the Commitment scheme with the types *)
clone import Commitment as CM with
  type CommitmentProtocol.value      <- matrix,
  type CommitmentProtocol.message    <- vector,
  type CommitmentProtocol.commitment <- vector,
  type CommitmentProtocol.openingkey <- vector.
export CommitmentProtocol.

module JKPT12 : CommitmentScheme = {
  proc gen() : matrix = {
  var a;
  a <$ dmatrix dR k l `*` dmatrix dR k v;
  return a.`1||a.`2;
  }

  proc commit(h: matrix, m: vector) : vector * vector = {
    var c, r, e;
    r <$ dvector dR l; 
    e <$ chi;
    c <- h *^ (catv r m) + e;
    return (c, r);
  }

  proc verify(h: matrix, m: vector, c: vector, d: vector) : bool = {
    var e;
    e <- c - (h*^ (catv d m));
    return (checkW e /\ size c = rows h);
  }
}.

section JKPT12Security.

  (* The commitment scheme is correct *)
  lemma JKPT12_correctness:
    hoare[Correctness(JKPT12).main: true ==> res].
  proof.
    proc. inline *. wp. rnd. rnd. wp. rnd. auto. progress.

    (* weight matches *)
    have : (a.`1||a.`2) *^ (r0 || m{hr}) + e1 - (a.`1||a.`2) *^ (r0 || m{hr}) = e1.  rewrite addvC.
    rewrite addvA. rewrite (addvC (- (a.`1||a.`2) *^ (r0 || m{hr}))). rewrite addvN.
    have : (size ((a.`1||a.`2) *^ (r0 || m{hr}))) = size e1. rewrite size_mulmxv. rewrite chi_k; trivial.
    apply dProdMatrixSize  in H. smt(@M).
    have : size ((a.`1||a.`2) *^ (r0 || m{hr}) + e1) = size ((a.`1||a.`2) *^ (r0 || m{hr})).
    rewrite size_addv. rewrite (chi_k e1). smt(). rewrite size_mulmxv. apply dProdMatrixSize  in H. smt(@M).
     move => h1. move => h. rewrite h. smt(@M). move => h. rewrite h. smt(chi_weight).
   
    (* size meets *)
    rewrite size_addv. apply dProdMatrixSize in H. smt(@M chi_k).
qed.


(* The commitment scheme is perfectly binding *)
lemma JKPT12_computational_binding (B<:Binder) &m: 
  islossless B.bind  =>
  Pr[BindingExperiment(JKPT12, B).main() @ &m : res] <= mDist k l v.
proof.
  move => Ab_ll. byphoare => //. proc. inline*.

  (* We need to check we aren't in the case where matrix doesn't prodcue codes with sufficent distance *)
  seq 1 : (forall y y', w+w < weight ((a.`1 || a.`2) *^ y - (a.`1 || a.`2) *^ y') /\
  a \in dmatrix dR k l `*` dmatrix dR k  JKPT12_aux.v)
  (1%r -  (mDist k l JKPT12_aux.v)) 0%r (mDist k l JKPT12_aux.v) 1%r. auto. 

  (* When we get a good generator then binding holds *)
  auto. hoare. call(_ : true). auto. progress. move => @/checkW. 
  case (weight (result.`1 - (a{hr}.`1 || a{hr}.`2) *^ (result.`3 || result.`2)) = w) => h.
  case (weight (result.`1 - (a{hr}.`1 || a{hr}.`2) *^ (result.`5 || result.`4)) = w) => h'. case (result.`2 = result.`4) => h''.
  smt(). case (size result.`1 = rows (a{hr}.`1 || a{hr}.`2)) => h'''. auto.
  (* main case *)
    simplify.
  have : w + w < weight ((a{hr}.`1 || a{hr}.`2) *^ (result.`3 || result.`2) - (a{hr}.`1 || a{hr}.`2) *^ (result.`5 || result.`4)).
  smt(). move => g.
  (* Prove weight bound *)
    have : (result.`1 - (a{hr}.`1 || a{hr}.`2) *^ (result.`3 || result.`2) -
    (result.`1 - (a{hr}.`1 || a{hr}.`2)  *^ (result.`5 || result.`4))) =
  (a{hr}.`1 || a{hr}.`2) *^ (result.`5 || result.`4) - (a{hr}.`1 || a{hr}.`2) *^ (result.`3 || result.`2). 
    rewrite (addvC result.`1). rewrite - addvA.
    rewrite oppvD. rewrite (addvA result.`1). rewrite addvN. rewrite h'''.
    have : rows (a{hr}.`1 || a{hr}.`2) = size ((a{hr}.`1 || a{hr}.`2)*^ (result.`5 || result.`4)).
    rewrite size_mulmxv. trivial. move => h5. rewrite h5. rewrite oppvK. rewrite add0v. rewrite addvC. trivial.
  move => h6.
    have : weight ((result.`1 - (a{hr}.`1 || a{hr}.`2) *^ (result.`3 || result.`2)) -
    (result.`1 - (a{hr}.`1 || a{hr}.`2) *^ (result.`5 || result.`4))) <= w+w.
    rewrite - {1} h. rewrite - h'. apply weightSub. move => h4. rewrite h6 in h4. smt().
  (* clean up *)
  auto.  auto.  auto.  

  (* case from early sequence *)
    rnd. auto. progress. rewrite mu_not. rewrite aDistance. smt(@Distr).  auto. progress. 
qed. 

(* The commitment scheme is comp. hiding *)
 
module type Adversary = {
  proc distinguish(mA: matrix, t: vector) : bool
}.

  module Attacker(U:Unhider) : Adversary = {
    proc distinguish(mA: matrix, t: vector) : bool= {
      var m0, m1, b, b', a'';
      a'' <$ dmatrix dR k v;
      (m0, m1) <@ U.choose(mA||a'');
       b        <$ {0,1};
       b'       <@ U.guess(a'' *^ ((b?m1:m0)) + t);
      return b' = b;
    }
  }.

 local lemma hiding_mlwe0 (A<:Unhider) &m:
    islossless A.choose =>
      islossless A.guess =>
      Pr[HidingExperiment(JKPT12,A).main() @ &m : res] =
      Pr[GameL(Attacker(A)).main() @ &m : res].
  proof.
    move => Ac_ll. move => Ag_ll. byequiv =>//. proc. inline *. wp.
    (* prove equality of generators *)
    swap {2} 6 -4. seq 1 2 : (={glob A} /\ a{1}.`1 =mA{2} /\ a{1}.`2 = a''{2} /\
    a{1}.`1 \in dmatrix dR k l /\ a{1}.`2 \in dmatrix dR k v). rnd : 0 0. progress. auto. progress.
  by rewrite -dprod_dlet dmap_id => />; case. rewrite -dprod_dlet. smt(@Distr). smt(@Distr). smt(@Distr).
    (* resume main *)
    swap{1} [6..7] -4. call(_:true). wp. rnd. call(_:true). auto. progress. 
     rewrite addvA. rewrite (addvC (a{1}.`2 *^ if bL then result_R.`2 else result_R.`1)).
    rewrite mulmxv_cat. smt(@MLWE). trivial.  smt().
qed.

  local module Gb (A:Unhider)  = {
    proc main () : bool = {
      var mA, t, a'', m0, m1, b, b';
      mA <$ dmatrix dR k l;
      t <$ dvector dR k;
      a'' <$ dmatrix dR k v;
      (m0, m1) <@ A.choose(mA||a''); 
      b'       <@ A.guess(t);
      b        <$ {0,1};
      return b' = b;
    }
  }.

  local lemma hiding_gb (A<:Unhider) &m:
    islossless A.choose =>
      islossless A.guess =>
      Pr[GameR(Attacker(A)).main() @ &m : res] =
      Pr[Gb(A).main() @ &m : res].
  proof.
    move => Ac_ll. move => Ag_ll. byequiv =>//. proc. inline *.
    swap{1} 5 -3. swap{2} 2 2. swap{1} 5 1. swap{1} 3 2. 
    swap{1} 7 -2. swap{2} 6 -2. wp. auto; call (_:true). wp.

    (* start sampling coins *)
    rnd (fun z, z + a''{1} *^ if b{1} then m1{1} else m0{1})
  (fun z, z - a''{2} *^ if b{2} then m1{2} else m0{2}). rnd.
    auto; call (_:true). wp. rnd. rnd. auto. progress.
    have : size (a''L *^ if bL then result_R.`2 else result_R.`1) =k. rewrite (size_mulmxv). have: size a''L =(k,v).
    apply (size_dmatrix dR); trivial. smt(gt0_k). smt(@Int gt0_l gt0_v). smt(). move =>h. have: size tR=k.
    smt(size_dvector). move=>h'.
    have : - a''L *^ (if bL then result_R.`2 else result_R.`1) +a''L *^ (if bL then result_R.`2 else result_R.`1) = zerov k.
    rewrite addvC. smt(addvN). move => h''.
    have : tR - a''L *^ (if bL then result_R.`2 else result_R.`1) + a''L *^ (if bL then result_R.`2 else result_R.`1) = tR.
    rewrite addvC. rewrite addvA. rewrite addvC. rewrite addvA. rewrite h''. smt(lin_add0v). smt().

    have: size tR=k. rewrite (size_dvector dR k tR).  smt(). smt(gt0_k). move => g.  have: k= size tR. smt(). move=> g'.

    have : size (a''L *^ if bL then result_R.`2 else result_R.`1) =k. rewrite (size_mulmxv). have: size a''L =(k,v).
    apply (size_dmatrix dR); trivial. smt(gt0_k). smt(@Int gt0_l gt0_v). smt(). move =>h.
    have : k = size (tR - a''L *^ if bL then result_R.`2 else result_R.`1). smt(size_addv) . move =>  h'. rewrite h'.
    rewrite mu1_dvector_fu. apply dR_funi. rewrite -h'. rewrite g'.
    rewrite mu1_dvector_fu. apply dR_funi. trivial.

    have : size (a''L *^ if bL then result_R.`2 else result_R.`1) =k. rewrite (size_mulmxv).
    have: size a''L =(k,v). apply (size_dmatrix dR); trivial. smt(gt0_k). smt(@Int gt0_l gt0_v). smt(). move =>h.

  have: size rL=k. rewrite (size_dvector dR k rL).  smt(). smt(gt0_k). move => g.

    have :  size (rL + a''L *^ if bL then result_R.`2 else result_R.`1) =k . smt(size_addv) . move => f.
    rewrite -f. apply (dvector_fu dR (rL + a''L *^(if bL then result_R.`2 else result_R.`1))  ). smt(dR_ll dR_funi @Distr). 
 
    have : size (a''L *^ if bL then result_R.`2 else result_R.`1) =k. rewrite (size_mulmxv). have: size a''L =(k,v).
    apply (size_dmatrix dR); trivial. smt(gt0_k). smt(@Int gt0_l gt0_v). smt(). move =>h.
    have : a''L *^ (if bL then result_R.`2 else result_R.`1) -a''L *^ (if bL then result_R.`2 else result_R.`1) = zerov k.
    smt(addvN). move => h'.
    have : rL + a''L *^(if bL then result_R.`2 else result_R.`1) -a''L *^(if bL then result_R.`2 else result_R.`1) =rL.
    rewrite addvC. rewrite addvA. rewrite addvC. rewrite addvA. rewrite h'. have: size rL=k. rewrite (size_dvector dR k rL).
    smt(). smt(gt0_k). move => g. smt(lin_add0v). smt(). rewrite(addvC). trivial.
  qed.    
  
  local lemma hiding_mlwe1 (A<:Unhider) &m: 
    islossless A.choose =>
      islossless A.guess =>
      Pr[Gb(A).main() @ &m : res] = 1%r/2%r.
  proof.
    move => Ac_ll Ag_ll. byphoare=> //; proc.
    rnd  (pred1 b')=> //=.
    conseq (: _ ==> true). progress. smt. smt(). 
    islossless. apply dmatrix_ll. apply dR_ll. apply dvector_ll. apply dR_ll.
    apply dmatrix_ll. apply dR_ll.
  qed.
  
  lemma JKPT12_comp_hiding (U<:Unhider) &m:
    islossless U.choose =>
    islossless U.guess =>
      Pr[HidingExperiment(JKPT12,U).main() @ &m : res]  - 1%r / 2%r =
      Pr[GameL(Attacker(U)).main() @ &m :res]-Pr[GameR(Attacker(U)).main() @ &m : res].
    proof.
      move => Ac_ll. move => Ag_ll. rewrite (hiding_mlwe0 U &m). smt(). smt().
      rewrite (hiding_gb U &m). smt(). smt(). rewrite (hiding_mlwe1 U &m). smt(). smt(). trivial.
    qed.


  end section JKPT12Security.
