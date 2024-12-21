require import AllCore Distr DInterval  IntDiv List Perms.

require (*--*) SigmaProtocol3 Commitment_aux.
require (*--*) MLWE.

import MLWE.
import M.

require JKPT12_com.
import JKPT12_com.

clone import Commitment_aux as CP with
  type CommitmentProtocol.aux <- (matrix * vector)*(vector * vector)*int,
  type CommitmentProtocol.message <- vector.
export CommitmentProtocol.

 clone import SigmaProtocol3 as SP with
  type  SigmaProtocol.statement <- matrix * vector, (* matrix A and commtiment y and key *)
  type SigmaProtocol.witness    <- vector * vector, (* vectors r and m *) 
  type SigmaProtocol.message <- key*commitment*commitment*commitment*commitment, (* C0, C1, C2 *) 
  type SigmaProtocol.secret <-
      (int list) * vector * vector *vector*vector*vector* opening * opening * opening*opening , (* pi, v, f *)
  type SigmaProtocol.response <- int list*vector*vector*opening*opening*opening*vector, (*  *)
  op SigmaProtocol.R = fun (m : matrix * vector)(w : vector * vector) =>
    checkW  (m.`2 - (m.`1 *^ (catv w.`2 w.`1))) /\ size m.`2 = rows m.`1 /\ rows m.`1 = k /\ v + l = cols m.`1 /\
  size w.`2 = l /\  size w.`1 = v,
  op SigmaProtocol.de = (duniform (range 0 3)).
  export SigmaProtocol.

  
  module ValidOpeningProt  : SigmaScheme ={
  proc gen() : (matrix*vector)*(vector*vector) = {
    var a, m, c, d;
    a <@ JKPT12.gen();
    m <$ dvector dR v; 
    (c, d) <@ JKPT12.commit(a,m);
    return ((a,c),(m,d));
  }

  proc commit (h: matrix*vector, w: vector*vector) :
  (key*commitment*commitment*commitment*commitment)*
  (int list*vector*vector*vector*vector*vector*opening*opening*opening*opening) ={
      var pi, vBold, f, c, c0, c1, c2, e, d, d0, d1, d2,t0,t1,t2, r1, r2, r3, r4, key;
      pi <$ (duniform (allperms (range 0 k)));
      vBold <$ dvector dR (l+v);
      f <$ dvector dR k;
      r1 <$ commit_rand;
      r2 <$ commit_rand;
      r3 <$ commit_rand;
      r4 <$ commit_rand;
      e <- h.`2 - (h.`1 *^ (catv w.`2 w.`1));
      t0 <-  h.`1 *^ vBold + f;
      t1 <- permVector (- f) pi;
      t2 <-  permVector (-(f + e)) pi;
      key <$ keygen;    
      (c, d) <- commit key (permToVector pi) r1;
      (c0,d0) <- commit key (h.`1 *^ vBold + f) r2;
      (c1,d1) <- commit key (permVector (- f) pi) r3; 
     (c2,d2) <- commit key (permVector (-(f + e)) pi) r4; 
    return ((key,c,c0, c1, c2),(pi,vBold,f,t0,t1,t2,d,d0,d1,d2));
    }
  
   proc test (h : matrix * vector, w:  key*commitment*commitment*commitment*commitment) : int ={
      var c;
      c <$ (duniform (range 0 3));
      return c;
  }

  proc respond (sw : ( matrix * vector)*(vector * vector), ms : (key*commitment*commitment*commitment*commitment)*
    (int list*vector*vector*vector*vector*vector*opening*opening*opening*opening),
      e : int) :  int list*vector*vector*opening*opening*opening*vector ={
                           (*perm,    t0,       t1,        d,       d0,         d1, v*)
    return ( if (e=0) then (ms.`2.`1, ms.`2.`4 , ms.`2.`5, ms.`2.`7, ms.`2.`8,  ms.`2.`9, ms.`2.`2)
                           (*perm,    t0,       t2,       d,        d0           d2, v *)
      else if (e=1) then   (ms.`2.`1, ms.`2.`4, ms.`2.`6, ms.`2.`7, ms.`2.`8, ms.`2.`10,
        ms.`2.`2 + (catv sw.`2.`2 sw.`2.`1)) else
      ([], ms.`2.`5 , ms.`2.`6, ms.`2.`9,  ms.`2.`9, ms.`2.`10, zerov (l+v)) );
  }
  
  proc verify (x:(matrix * vector) , m:(key*commitment*commitment*commitment*commitment), e:int ,
      z: (int list*vector*vector*opening*opening*opening*vector)) : bool ={
      var resp0, resp1, resp2, resp3, resp4;
      if (e=0) {
      resp0 <- verify m.`1 (permToVector z.`1) (m.`2, z.`4);
      resp1 <- verify m.`1 z.`2 (m.`3, z.`5);
      resp2 <- verify m.`1  z.`3 (m.`4, z.`6);
      resp3 <- x.`1*^ z.`7 = (z.`2 +  permVector  z.`3 (invPerm z.`1));
      resp4 <- isPerm z.`1;
    }
    
    else { if (e=1) {
        resp0 <- verify m.`1 (permToVector z.`1) (m.`2, z.`4);
        resp1 <- verify m.`1 z.`2 (m.`3, z.`5) ;
        resp2 <- verify m.`1  z.`3 (m.`5, z.`6); 
        resp3 <- x.`1*^z.`7 =  (z.`2 +  (permVector  z.`3 (invPerm z.`1)) + x.`2 );
        resp4 <- true;  }
    
      else { if (e=2) {
        resp0 <- true;
        resp1 <- verify m.`1 z.`2 (m.`4, z.`5) ;
        resp2 <- verify m.`1 z.`3 (m.`5, z.`6); 
        resp3 <-checkW (z.`2-z.`3) ;
        resp4 <- true;  }}}
    
    return resp0 /\ resp1 /\ resp2 /\ resp3 /\ resp4 /\ size x.`2 = rows x.`1 /\ rows x.`1 = k /\ v + l = cols x.`1
    /\ size z.`2 = k /\ size z.`3 = k /\ size z.`7 = (l+v);
  } 
}.
module ValidOpenAlg : SigmaAlgorithms ={
  proc soundness (h: matrix*vector, m :  key*commitment*commitment*commitment*commitment,
  z:int list*vector*vector*opening*opening*opening*vector, z': int list*vector*vector*opening*opening*opening*vector,
  z'': int list*vector*vector*opening*opening*opening*vector) : (vector*vector) option ={
    var rCatM;
    rCatM <- z'.`7 -z.`7;
    return Some (subv rCatM l (l+v), subv rCatM 0 l);
  }

  proc simulate (h: matrix*vector, e: int) : (key*commitment*commitment*commitment*commitment)*
    (int list*vector*vector*opening*opening*opening*vector) = {
      var pi,vBold,f,b;
      var t0,t1,d,d1,d2,d3,c,c1,c2,c3, r1,r2,r3,r4,key;

      key <$ keygen;
      pi <$ (duniform (allperms (range 0 k)));
      vBold <$ dvector  dR (l +  v);            
      f <$ dvector dR k;
      b <$ chi;
      r1 <$ commit_rand;
      r2 <$ commit_rand;
      r3 <$ commit_rand;
      r4 <$ commit_rand;
      
      t0 <-  h.`1 *^ vBold + f;
      t1 <- permVector (- f) pi;
      (c, d) <- commit key (permToVector pi) r1;
      (c1,d1) <- commit key (h.`1 *^ vBold + f) r2;
      (c2,d2) <- commit key (permVector (- f) pi) r3;
      (c3,d3) <- commit key (permVector (f + b) pi) r4;

      if (e=0) {
        (c3, d3) <- commit key (zerov (l+v)) r4;
      }
      if (e=1) {
        (c1,d1) <- commit key (h.`1 *^ vBold + f + h.`2) r2;
        (c2,d2) <- commit key (zerov (l+v)) r3;
        (c3,d3) <- commit key (permVector f pi) r4;
      }
      if (e=2) {
        (c,d) <- commit key (zerov (l+v)) r1;
        (c1,d1) <- commit key (zerov (l+v)) r2;
      }
  
        
      
     return ( if (e=0) then ((key,c,c1,c2,c3),(pi, t0, t1, d, d1, d2, vBold))
     else if (e=1) then ((key,c,c1,c2,c3),(pi, ( h.`1 *^ vBold + f + h.`2),
        permVector (-f) pi, d, d1, d3, vBold)) else
     ((key,c,c1,c2,c3),([], t1, permVector (-f+b) pi, d2, d2, d3, zerov (l+v))));
  }
}.


module SimulatorCorrDef ={
  proc main (h : matrix*vector, e:int) : bool = {
    var tran, b;
    tran <@ ValidOpenAlg.simulate(h,e);
    b <@ ValidOpeningProt.verify(h,tran.`1,e,tran.`2);
    return b;
  }
}.

lemma probSimp (p : 'a -> bool)(k : 'a distr) : p = predT => mu k p = mu k predT.
    auto.
qed.

section Protocol_Security.

lemma ValidOpenProt_Completeness s w' &m:
  R s w' =>
  Pr[Completeness(ValidOpeningProt).main(s, w') @ &m  : res] = 1%r.
  proof.
  move => @/R. move => h. byphoare (: arg = (s, w') ==> res) => //.
    conseq (: true ==> true: =1%r)(: arg = (s, w') ==> res). auto.
    (* correctness *)
    proc. inline *. auto. progress.
    (* case 0 *)
    smt(commit_verify_correct). smt(commit_verify_correct). smt(commit_verify_correct).
      (* Checking new version of inImage *)
    rewrite permVectorInv. smt(@Distr @Perms @List).  rewrite size_oppv. have : size f0 = k. smt(@MLWE.M). move => h'.
    rewrite h'. have : perm_eq pi0 (range 0 k). smt(@Distr @Perms @List). move => h''.
    smt(@List gt0_k). rewrite -addvA. rewrite addvN. rewrite lin_addv0.
    smt(@MLWE.M). smt(@MLWE.M). smt(@Distr @Perms @List). smt(). smt(). smt(). smt(@MLWE.M). apply permVectorSize.
    smt(@List @Distr @Perms). smt(@MLWE.M).
    (* case 1 *)
    smt(commit_verify_correct). smt(commit_verify_correct). smt(commit_verify_correct).
      (* Checking new version of inImage *)
    rewrite permVectorInv. smt(@Distr @Perms @List). have : perm_eq pi0 (range 0 k).  smt(@Distr @Perms @List).
    move => h''. smt(@List @MLWE.M gt0_k). rewrite oppvD. rewrite addvA. rewrite -(addvA _ f0).
    rewrite addvN. rewrite lin_addv0.  smt(@MLWE.M). 
    rewrite oppvD. rewrite oppvK.  rewrite -addvA. rewrite (addvC _ x{hr}.`2).
    rewrite addvA. rewrite (addvA _ (-x{hr}.`2)). rewrite -(addvA _ x{hr}.`2).
    rewrite addvN. rewrite lin_addv0. smt(@MLWE.M). smt(@MLWE.M). smt(). smt(). smt(). smt(@MLWE.M).
    apply permVectorSize. smt(@List @Distr @Perms). smt(@M).
    (* case 2 *)
    smt(commit_verify_correct). smt(commit_verify_correct). 
    have : forall v v' pi1, isPerm pi1 => size pi1 = size%Vectors v => size pi1 = size%Vectors v' =>
    permVector v pi1 - permVector v' pi1 = permVector (v - v') pi1. move => v v' pi1 g g' g''. rewrite -permVectorAdd; auto. 
    rewrite  permVectorOp. trivial. trivial. move => g. rewrite g; auto. smt(@List @Distr @Perms).
    have : perm_eq pi0 (range 0 k).  smt(@Distr @Perms @List). move => h''. smt(@Distr @Perms @List @MLWE.M).
    have : perm_eq pi0 (range 0 k).  smt(@Distr @Perms @List). move => h''. rewrite size_oppv.
    rewrite size_addv. apply pi_c_m_size. smt(). smt(). smt(). rewrite -checkWPerm. smt(@List @Distr @Perms).
    smt(@M).
    rewrite oppvK. rewrite addvA. rewrite (addvC _ f0). rewrite addvN. rewrite lin_add0v. apply f_c_m_size.
    smt(). smt(). smt(). smt(). smt(). smt(). apply permVectorSize. smt(@Distr @List @Perms). apply permVectorSize.
    smt(@Distr @List @Perms). smt(gt0_k gt0_v). 
    (* stupid case *)
    smt(@Distr). smt(@Distr). smt(@Distr). smt(@Distr). smt(@Distr). smt(@Distr). smt(@Distr). smt(@Distr). smt(@Distr).
    smt(@Distr). smt(@Distr).
    (* termination *)
    proc. inline *. auto. progress. apply duniform_ll. apply permNotEmpty.
    smt(@MLWE.M dR_ll). smt(@MLWE.M dR_ll). apply commit_rand_ll. apply keygen_ll.
    rewrite duniform_ll. smt(@List). trivial.
qed.

  (* Binding is perfect *)
  lemma ValidOpenProt_Sound (F <: SigmaFaker)  &m:
    hoare[SpecialSoundnessExperiment(ValidOpeningProt, ValidOpenAlg, F).main : true ==> res].
  proof.
    proc. inline*. auto. call(_:true). auto. progress; trivial. clear H4 H5 H6 H8 H14 H15 H16 H17 H18.
    (* Lets simplifier the variables in the lemmas *)
    have :  result.`3.`1 = result.`4.`1. apply permToVectorInj. apply (commit_verify_sound _ _ _ _ _ _ H H10); auto.
    move => G. have : result.`3.`2 = result.`4.`2. apply (commit_verify_sound _ _ _ _ _ _ H0 H11);
    auto. move => G'. simplify. have : result.`3.`3 =  result.`5.`2.
    apply (commit_verify_sound _ _ _ _ _ _ H1 H20); auto. move => G''.
    have : result.`4.`3 =  result.`5.`3.  apply (commit_verify_sound _ _ _ _ _ _ H12 H21); auto. move => G'''.
    clear H H0 H1 H10 H11 H12 H20 H21. 
    (* Need to prove basic result *)
    rewrite catv_subvC_gen. smt(@MLWE.M). smt(@MLWE.M gt0_l gt0_v).
    have : result.`1.`1 *^  (result.`4.`7 - result.`3.`7) =
    (result.`1.`2 + permVector (- result.`5.`2 + result.`5.`3) (invPerm result.`4.`1)).
     have : result.`1.`1 *^ (result.`4.`7 - result.`3.`7) =
  ((result.`3.`2 + permVector result.`3.`3 (invPerm result.`3.`1)) +
    (result.`4.`2 + permVector result.`4.`3 (invPerm result.`4.`1) + result.`1.`2)).
    rewrite mulmxvDr. rewrite bRing. rewrite H2. rewrite H13. smt(@MLWE.M).  move => h''. rewrite h''. rewrite G'. rewrite G.
      rewrite G''. rewrite G'''. have : forall (a b c d : vector), size a = size b => a + b + (a + c + d) = (b + c) + d.
    move => a b c d h. rewrite addvA. have : forall (a b c : vector), a = b => a +c = b + c. smt(@MLWE.M). move => g. apply g.
      rewrite addvA. apply g. pose e := (a + b). rewrite -(bRing a). move => @/e. rewrite (addvC _ b). rewrite -addvA.
    rewrite addvN. rewrite lin_addv0. trivial. trivial.
     move => h'''. rewrite h'''. smt(@List @MLWE.M). rewrite permVectorAdd; trivial. apply invPermPerm. smt().
      smt(@List @MLWE.M). smt(@List @MLWE.M). smt(@MLWE.M bRing). move => h''. rewrite h''. 
    (* Fist case *)
    rewrite oppvD. rewrite addvA. rewrite addvN. rewrite lin_add0v. rewrite H23. rewrite H24.
    rewrite size_oppv. smt(@MLWE.M @List gt0_k). rewrite permVectorOp. rewrite -G. apply invPermPerm. trivial.
      rewrite oppvD. rewrite oppvK.  rewrite -checkWPerm. trivial. apply invPermPerm. smt(@Distr @List @Perms).
    smt(@M). smt(weightSub). smt(@M gt0_l). smt(@M gt0_v).
qed.

  (* We now need to introduce a game which sits between simulate and real but which only differs from real in that the
      commitments and responses are the same as in simulate  *)
  module GB (D : Decider) = {
    proc main (h : matrix * vector, w : vector * vector, e: int) : bool = {
      var pi, vBold, f,bW, c, c1, c2, c3, d, e1, d1, d2,d3, t0,t1,t2, r1, r2, r3, r4, com, resp, b, key;
      
      key <$ keygen;  
      pi <$ (duniform (allperms (range 0 k)));
      vBold <$ dvector dR (l+v);
      f <$ dvector dR k;
      bW <$ chi;
      
      r1 <$ commit_rand;
      r2 <$ commit_rand;
      r3 <$ commit_rand;
      r4 <$ commit_rand;
      
      e1 <- h.`2 - (h.`1 *^ (catv w.`2 w.`1));
      t0 <-  h.`1 *^ vBold + f;
      t1 <- permVector (- f) pi;
      t2 <-  permVector (-(f + e1)) pi;

      (* Honest commitment generation 
      (c, d) <- commit h.`3 (permToVector pi) r1;
      (c0,d0) <- commit h.`3 (h.`1 *^ vBold + f) r2;
      (c1,d1) <- commit h.`3 (permVector (- f) pi) r3; 
      (c2,d2) <- commit h.`3 (permVector (-(f + e1)) pi) r4;
      com <- (c,c0,c1,c2); *)

      (* Simulated commitment generation *)
      
      (c, d) <- commit key (permToVector pi) r1;
      (c1,d1) <- commit key (h.`1 *^ vBold + f) r2;
      (c2,d2) <- commit key (permVector (- f) pi) r3;
      (c3,d3) <- commit key (permVector (f + bW) pi) r4;

      if (e=0) {
        (c3, d3) <- commit key (zerov (l+v)) r4;
      }
      if (e=1) {
        (c1,d1) <- commit key (h.`1 *^ vBold + f + h.`2) r2;
        (c2,d2) <- commit key (zerov (l+v)) r3;
        (c3,d3) <- commit key (permVector f pi) r4;
      }
      if (e=2) {
        (c,d) <- commit key (zerov (l+v)) r1;
        (c1,d1) <- commit key (zerov (l+v)) r2;
      }
        
      com <- (key,c,c1,c2,c3);
        
                                 (*perm,    t0,       t1,        d,       d0,         d1, v*)
      resp <- ( if (e=0) then (pi, t0 , t1, d, d1,  d2, vBold)
                           (*perm,    t0,       t2,       d,        d0           d2, v *)
      else if (e=1) then   (pi,  h.`1 *^ vBold + f + h.`2, permVector (- f) pi, d, d1, d3,  vBold) else
      ([], t1 , permVector (-f+bW) pi, d2,  d2, d3, zerov (l+v)) );
      b <@ D.distinguish(h,com,e,resp);
      return b;
    }
  }.

  (* The reduction from the ZK adversary to the commitment scheme adversary *)
  module U (D : Decider) : Unhider = {
    var ck : key
    var pi : int list
    var vBold : vector
    var f : vector
    var bW : vector
    
    proc choose(x:key,a:(matrix*vector)*(vector*vector)*int) = {
      var e1;
      
      pi <$ (duniform (allperms (range 0 k)));
      vBold <$ dvector dR (l+v);
      f <$ dvector dR k;
      bW <$ chi;

      ck <- x;

      e1 <- a.`1.`2 - (a.`1.`1 *^ (catv a.`2.`2 a.`2.`1));
      return ((zerov (l+v), zerov (l+v)),
        (if (a.`3 = 2) then (permToVector (composePerm (invPerm (findPermEq e1 bW)) pi)) else permVector (-(f + e1)) pi,
          if (a.`3 = 1) then  (permVector (-f + (a.`1.`2 - a.`1.`1 *^ (a.`2.`2 || a.`2.`1))) pi)
          else a.`1.`1 *^ vBold + (permVector f  (findPermEq e1 bW))));
    }

    proc guess(c:commitment*commitment,a:(matrix*vector)*(vector*vector)*int) = {
      var c0,c1,c2,c3,d0,d1,d2,d3, r1, r2, r3, r4, b, com, resp;

      r1 <$ commit_rand;
      r2 <$ commit_rand;
      r3 <$ commit_rand;
      r4 <$ commit_rand;
      
      (c0, d0) <- commit ck (permToVector pi) r1;
      (c1, d1) <- if (a.`3=1) then commit ck (a.`1.`1 *^ vBold + f + a.`1.`2) r2 else
         commit ck (a.`1.`1 *^ vBold + f) r2;

      (c2,d2) <- commit ck (permVector (- f) pi) r3;
      (c3,d3) <- if(a.`3 = 1) then commit ck (permVector (f) pi) r4 else commit ck (permVector (f + bW) pi) r4;

      com <- if (a.`3 = 0) then (ck,c0,c1,c2,c.`1) else (
        if (a.`3 = 1) then (ck,c0,c1,c.`2,c3) else (ck,c.`1,c.`2,c2,c3));

      resp <- if (a.`3=0) then (pi, a.`1.`1 *^ vBold + f,  permVector (- f) pi, d0, d1,  d2, vBold) else 
        (if (a.`3=1)then
       (pi, a.`1.`1 *^ vBold + f + a.`1.`2, permVector (- f) pi, d0, d1,  d3,
        vBold) else 
          ([], permVector (-f) pi,  permVector (-(f+ bW)) pi, d2, d2, d3, zerov (l+v)));  
      
      b <@ D.distinguish(a.`1, com,a.`3,resp);
      return b;
    }
  }.

  declare module D <: Decider {-U.ck, -U.f, -U.pi, -U.vBold, -U.bW}.


   local lemma Real_GB_0 s w e &m :
        e \in range 0 3 =>
        Pr[GB(D).main(s,w,e) @ &m : res] = Pr[HidingExperimentL(U(D)).main((s,w,e)) @ &m : res].
  proof.     
    move => Ran.     
    (* challenge case 0*)
    case(e = 0) => he1. subst. byequiv. proc. inline *. wp. call(_:true). wp. swap{2} [17..20] -6. wp. rnd{2}. rnd. rnd{2}.
    auto. progress. apply commit_rand_ll. auto. auto.
    (* challenge case 1 *)
    case(e = 1) => he2. subst. byequiv. proc. inline *. wp. call(_:true). wp. swap{2} [17..20] -6. wp. swap{2} 16 - 3. rnd{2}.
    rnd. rnd{2}.  auto. progress. apply commit_rand_ll. auto. auto.
    (* challenge case 2 *)
    have : (e =2). smt(@List). move => he3. subst. byequiv. proc. inline *. wp. call(_:true). wp. 
    swap{2} [19..20] -6. rnd{2}. rnd{2}. wp. auto. progress. apply commit_rand_ll. rewrite !bRing. trivial. auto. auto. 
 qed.

 local lemma c1_message_e1 (h : matrix*vector) (w : vector*vector) (vBold f : vector) : size f = size h.`2 => size f = rows h.`1 =>
   h.`1 *^ vBold + f = h.`1 *^ (vBold - (w.`2 || w.`1)) +
     (f - (h.`2 - h.`1 *^ (w.`2 || w.`1))) + h.`2.
  proof.    
    move => h0 h1. rewrite mulmxvDr. have : forall (v v' w w' : vector),v=v' => w=w' => v+ w=v' + w'. smt().
    move => h2. rewrite -addvA. rewrite -addvA.  rewrite -addvA. apply h2. trivial.
    rewrite (addvC (h.`1 *^ - (w.`2 || w.`1))). rewrite -addvA. rewrite -addvA. rewrite !bRing. rewrite addvA. apply bRing_cancel.
    smt(@MLWE.M).
  qed.
 
  local lemma t2_e2  (f : vector) (s: matrix*vector) (w: vector*vector) pi bW : isPerm pi => size f = k =>
    permVector f pi =
   permVector (permVector f (invPerm (findPermEq (s.`2 + s.`1 *^ (w.`2 || w.`1)) bW)))
      (composePerm (findPermEq (s.`2 + s.`1 *^ (w.`2 || w.`1)) bW) pi).
  proof.    
    move => h' h. rewrite composePermCorrect; trivial. apply invPermPerm. apply findPermChecks. apply composePermPerm.
    apply findPermChecks. trivial. rewrite -composePermA.  apply invPermPerm. apply findPermChecks. apply findPermChecks. 
    trivial. rewrite composePermNeg. apply findPermChecks. rewrite composePermID; trivial.
  qed.
  
  local lemma t3_e2 (f : vector) (s: matrix*vector) (w: vector*vector) pi bW : isPerm pi => size f = k => size s.`2 = k =>
         rows s.`1 = k => arePermEq (s.`2 + s.`1 *^ (w.`2 || w.`1)) bW => size bW = k =>
      permVector ((f) + (s.`2 + s.`1 *^ (w.`2 || w.`1))) pi =
      permVector (permVector f
        (invPerm (findPermEq (s.`2 + s.`1 *^ (w.`2 || w.`1)) bW)) + bW)
      (composePerm (findPermEq (s.`2 + s.`1 *^ (w.`2 || w.`1)) bW) pi).
  proof.
    move => isPerm size_f size_s2 size_s1 permEq size_bW. rewrite eq_sym. rewrite -permVectorAdd. apply composePermPerm. 
    apply findPermChecks. trivial. rewrite permVectorSize. apply invPermPerm. apply findPermChecks. apply isPerm_size_k.
    apply composePermPerm. apply findPermChecks. trivial. rewrite isPerm_size_k.
    apply composePermPerm. apply findPermChecks. trivial. smt().

    rewrite -t2_e2; trivial. rewrite -!composePermCorrect; trivial. apply findPermChecks.
    rewrite -(findPermCorr _ _ permEq). rewrite permVectorAdd; trivial. rewrite isPerm_size_k; trivial.
    smt(). elim permEq => h h'. elim h' => h' [h'' h''']. rewrite h'. smt(isPerm_size_k).
  qed. 

  local lemma Real_GB_1 s w e &m :
        R s w =>
        e \in range 0 3 =>
        Pr[SHVZK(ValidOpeningProt, ValidOpenAlg, D).real(s,w,e) @ &m : res] =
        Pr[HidingExperimentR(U(D)).main((s,w,e)) @ &m : res].
  proof.
    move => @/R Rel Ran.
    (* challenge case 0 *)
    case(e = 0) => he1. subst. byequiv. proc. inline *. wp. call(_:true). wp. swap{1} 14 -13. wp. swap{2} [17..20] -6. wp.
    rnd{2}. rnd. rnd{2}. rnd. rnd. rnd. wp. rnd{2}. auto. progress. apply chi_ll. apply commit_rand_ll. auto. auto.
  
    (* challenge case 1 *)
    case(e = 1) => he2. subst. byequiv. proc. inline *. wp. call(_:true). wp.  swap{1} 14 -13. wp. swap{2} [17..20] -6. wp.
    swap{2} 16 - 3. rnd{2}. rnd.  rnd{2}.  rnd.  rnd. rnd. wp. rnd{2}.
      (* sample f *)  rnd(fun (f : vector), f - (s{2}.`2 - s{2}.`1 *^ (w{2}.`2 || w{2}.`1)))
     (fun (f : vector), f + (s{2}.`2 - s{2}.`1 *^ (w{2}.`2 || w{2}.`1))).
       (* sample vBold *)
     rnd(fun b, b - (w{2}.`2 || w{2}.`1))
     (fun b, b +  (w{2}.`2 || w{2}.`1)). 
     (* smaple pi *) rnd. auto. progress.
     (* sampling correct *)
     smt(@MLWE.M). apply dRmu1ins. smt(gt0_l gt0_v). trivial. smt(@MLWE.M). apply dRin. smt(@MLWE.M). smt(@MLWE.M).
     smt(@MLWE.M). apply dRmu1ins. apply gt0_k. trivial. smt(@MLWE.M). apply dRin. smt(@MLWE.M). smt(@MLWE.M).
     (* commitments and opening equal *)
     apply chi_ll. apply commit_rand_ll. (* c1 m *) rewrite (c1_message_e1 h{1} w{1} vBoldL fL). smt(@MLWE.M). smt(@MLWE.M).
     trivial. (* c2 m *) rewrite !bRing. rewrite -bRing_cancel. smt(@MLWE.M). trivial. rewrite !bRing. trivial.
     (* t1 *) apply c1_message_e1.  smt(@MLWE.M). smt(@MLWE.M). (* t3 *) rewrite !bRing. trivial. 
     rewrite (c1_message_e1 h{1} w{1} vBoldL fL). smt(@MLWE.M). smt(@MLWE.M). trivial. rewrite !bRing. trivial. rewrite bRing.
     trivial. auto. auto.
     
    (* challenge case 2 *)
    have : e =2. smt(@List). move => he3. subst. byequiv. proc. inline *. wp. call(_:true). wp. swap{1} 14 -13.
       swap{2} [19..20] -6. rnd{2}. rnd{2}. wp. rnd. rnd. rnd. rnd. wp. swap{2} 7 -3. 
    (* Sample f *) rnd(fun (f : vector),
     permVector (f) (invPerm (findPermEq (- (s{2}.`2 - s{2}.`1 *^ (w{2}.`2 || w{2}.`1))) U.bW{2})))
     (fun (f:vector),
     permVector (f) (findPermEq (- (s{2}.`2 - s{2}.`1 *^ (w{2}.`2 || w{2}.`1)))  U.bW{2})). 
     (* Sample vBold *) rnd.
     (* Sample pi *) rnd(fun pi, composePerm 
       (findPermEq (-(s{2}.`2 - s{2}.`1 *^ (w{1}.`2 || w{1}.`1))) (U.bW{2}) ) pi{2})
     (fun pi, (composePerm (invPerm
           (findPermEq (-(s{2}.`2 - s{2}.`1 *^ (w{1}.`2 || w{1}.`1))) (U.bW{2})))  pi{2} )). 
             (* Sample b0 *) rnd{2}. auto. progress.
    (* sampling correct *)
     apply chi_ll. rewrite -composePermA. apply findPermChecks. apply invPermPerm. apply findPermChecks. smt(@Perms @List @Distr).
     rewrite composePermNeg. apply findPermChecks.
     rewrite composePermID.  smt(@Perms @List @Distr). trivial. apply mu1Perm. smt(@Perms @List @Distr). apply composePermPerm.
             apply invPermPerm. apply findPermChecks. smt(@Perms @List @Distr). apply isPermSimp2. apply composePermPerm.
             apply findPermChecks. smt(@Perms @List @Distr).
     rewrite -composePermA. apply invPermPerm. apply findPermChecks. apply findPermChecks. smt(@Perms @List @Distr).
     rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  smt(@Perms @List @Distr). trivial. 
     (* samling f *) rewrite composePermCorrect. smt(@M). apply findPermChecks. apply invPermPerm. apply findPermChecks.
     rewrite composePermNeg. apply findPermChecks. rewrite permVectorID. smt(@MLWE.M @Distr).
     trivial. apply dRpermPres. apply findPermChecks. smt(@MLWE.M). apply dRpermPres2. smt(). apply invPermPerm.
     apply findPermChecks. rewrite composePermCorrect. smt(@M). apply invPermPerm. apply findPermChecks. apply findPermChecks.
     rewrite composePermNeg. apply findPermChecks.  rewrite permVectorID.
     smt(@MLWE.M @Distr). trivial. 
    (* commitments and opening equal *)
    apply commit_rand_ll. (* c0 m *) rewrite !bRing. rewrite -composePermA. apply invPermPerm. apply findPermChecks.
    apply findPermChecks. smt(@List @Distr @Perms). rewrite composePermNeg. apply findPermChecks. rewrite composePermID.
    smt(@List @Distr @Perms). trivial.
    (* c1 m *) rewrite composePermCorrect. smt(@M). apply invPermPerm. apply findPermChecks. apply findPermChecks. rewrite !bRing.
    rewrite composePermNeg. apply findPermChecks. rewrite permVectorID. smt(@M). trivial. 
    (* c2 m *) apply commit_message_eq. rewrite !bRing. apply t2_e2. smt(@List @Distr @Perms). smt(@M).
    (*c3 m *)
    rewrite !bRing. apply commit_message_eq. apply t3_e2; trivial. smt(@Perms @Distr @List). smt(@MLWE.M). smt(). 
    smt(). apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. elim Rel => Rel0 Rel. rewrite eq_sym. rewrite chi_weight.
    trivial. rewrite eq_sym. rewrite bRing in Rel0. smt(). smt(chi_k).
    (* t2 *) rewrite !bRing. apply t2_e2. smt(@Perms @Distr @List). smt(@MLWE.M).
    (* t3 *) rewrite !bRing. apply t3_e2; trivial. smt(@Perms @Distr @List). smt(@Distr @MLWE.M gt0_k). smt().
    smt(). apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. elim Rel => Rel0 Rel. rewrite eq_sym. rewrite chi_weight.
    trivial. rewrite eq_sym. rewrite bRing in Rel0. smt(). smt(chi_k).
    (* c2 - opening *) apply commit_open_eq. rewrite !bRing. apply t2_e2; trivial.  smt(@Perms @Distr @List). smt(@MLWE.M).
    (* c2 - opening *) apply commit_open_eq. rewrite !bRing. apply t2_e2; trivial. smt(@Perms @Distr @List). smt(@MLWE.M).
    (* c3- opeing *) rewrite !bRing. apply commit_open_eq. apply t3_e2; trivial. smt(@Perms @Distr @List).
    smt(@Distr @MLWE.M gt0_k). smt(). smt(). apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. elim Rel => Rel0 Rel.
    rewrite eq_sym. rewrite chi_weight. trivial. rewrite eq_sym. rewrite bRing in Rel0. smt(). smt(chi_k). auto. auto.
  qed. 

  local lemma Real_GB  s w e &m :
      R s w =>
      e \in range 0 3 =>
      Pr[GB(D).main(s,w,e) @ &m : res] - Pr[SHVZK(ValidOpeningProt, ValidOpenAlg, D).real(s,w,e) @ &m : res]
      <= Pr[HidingExperimentL(U(D)).main((s,w,e)) @ &m : res] - Pr[HidingExperimentR(U(D)).main((s,w,e)) @ &m : res]. 
   proof.
     move => @/R Rel Ran. rewrite (Real_GB_0 s w e &m); trivial. rewrite (Real_GB_1 s w e &m); trivial.  
   qed. 

   lemma ValidOpen_ZK_sub s w e (D <: Decider) &m :
       R s w =>
       e \in range 0 3 =>
       islossless D.distinguish =>
       Pr[SHVZK(ValidOpeningProt, ValidOpenAlg, D).simulate(s,e) @ &m : res] = 
       Pr[GB(D).main(s,w,e) @ &m : res].
   proof. 
     move => @/R Rel Ran ll.
     (* case 0 *)
     case (e = 0). move => he. rewrite he.  byequiv => //. proc. call(_:true). inline *. wp. 
     auto. progress. 
   
     (* case 1 *)
     case (e = 1). move => h1. rewrite h1. byequiv => //. proc.  call(_:true). inline *. wp. auto. progress. 
      
     (* case 2 *)
     have : e = 2. smt(@List). move => h2. rewrite h2. byequiv => //. proc. call(_:true). inline *. wp.
     auto.
   qed.
 
   lemma ValidOpen_ZK s w e &m :
       R s w =>
       e \in range 0 3 =>
       islossless D.distinguish =>
       Pr[SHVZK(ValidOpeningProt, ValidOpenAlg, D).simulate(s,e) @ &m : res] -
       Pr[SHVZK(ValidOpeningProt, ValidOpenAlg, D).real(s,w,e) @ &m : res] <=
       Pr[HidingExperimentL(U(D)).main((s,w,e)) @ &m : res] - Pr[HidingExperimentR(U(D)).main((s,w,e)) @ &m : res].
    proof.
      move => h he d_ll. rewrite (ValidOpen_ZK_sub s w e D &m); trivial. apply (Real_GB s w e &m); trivial.
    qed.
