require import AllCore Distr DInterval  IntDiv List Perms.

require (*--*) Commitment.

require (*--*) SigmaProtocol3 Commitment_aux.
require (*--*) MLWE.

import MLWE.
import M.

require JKPT12_com.
import JKPT12_com.

clone import Commitment_aux as CP with
type CommitmentProtocol.aux <- (matrix * (vector*vector*vector) * matrix * matrix)*
    ((vector * vector * vector) *(vector*vector*vector))*int,
  type CommitmentProtocol.message <- vector*vector*vector.
export CommitmentProtocol.

clone import SigmaProtocol3 as SP with
  (* matrix A and commtiment y_0, y_1, y_2, X_1, X_2, and key *)
  type  SigmaProtocol.statement <- matrix * (vector *  vector *  vector) * matrix * matrix,
  (* vectors r_1, r_2, r_3 and m_1, m_2, m_3 *) 
  type SigmaProtocol.witness    <- (vector * vector * vector) * (vector * vector * vector),
  (* C0, C1, C2 *) 
  type SigmaProtocol.message <- key*commitment*commitment*commitment*commitment,
  type SigmaProtocol.secret <-
    ((int list) * (int list) * (int list)) * (vector * vector * vector) * (vector * vector*vector) *(vector*vector*vector)*
    (vector*vector*vector)*(vector*vector*vector)*opening*opening*opening*opening,
    type SigmaProtocol.response <- (int list*int list*int list)*
    (vector*vector*vector)*(vector*vector*vector)*opening*opening*opening*(vector*vector*vector), (*  *)
  op SigmaProtocol.R = fun (m : matrix * (vector *  vector *  vector) * matrix * matrix)
    (w : (vector * vector * vector) * (vector * vector * vector)) =>
      (* Valid commitments *)  
      checkW  (m.`2.`1 - (m.`1 *^ (catv w.`2.`1 w.`1.`1))) /\
      checkW  (m.`2.`2 - (m.`1 *^ (catv w.`2.`2 w.`1.`2))) /\
      checkW  (m.`2.`3 - (m.`1 *^ (catv w.`2.`3 w.`1.`3))) /\
      (* Messages constraint *)
      w.`1.`3 = m.`3*^w.`1.`1 + m.`4*^w.`1.`2 /\
      (* Commitments of expected size *)
      size m.`2.`1 = rows m.`1 /\ size m.`2.`2 = rows m.`1 /\  size m.`2.`3 = rows m.`1 /\
      (* Matrix of expected size *)
      rows m.`1 = k /\ l + v = cols m.`1 /\
      rows m.`3 = rows m.`4 /\
      (* Messages and randomness of expected size *)
      size w.`2.`1 = l /\  size w.`1.`1 = v /\
      size w.`2.`2 = l /\  size w.`1.`2 = v /\
      size w.`2.`3 = l /\  size w.`1.`3 = v,
    
  op SigmaProtocol.de = (duniform (range 0 3)).
  export SigmaProtocol.

  module LinearRelProt  : SigmaScheme ={
  proc gen() : (matrix * (vector *  vector *  vector) * matrix * matrix)*
    ((vector * vector * vector) * (vector * vector * vector)) = {
    var a, x1, x2, m1, m2, m3, c1, c2, c3, d1, d2, d3;
    a <@ JKPT12.gen();
    x1 <$ dmatrix dR v v;
    x2 <$ dmatrix dR v v;
    m1 <$ dvector dR v;
    m2 <$ dvector dR v;
    m3 <- x1 *^ m1 + x2 *^ m2;
    (c1, d1) <@ JKPT12.commit(a,m1);
    (c2, d2) <@ JKPT12.commit(a,m2);
    (c3, d3) <@ JKPT12.commit(a,m3);
    return ((a,(c1,c2,c3),x1,x2),((m1,m2,m3),(d1,d2,d3)));
  }

  proc commit (h: matrix * (vector *  vector *  vector) * matrix * matrix,
     w: (vector * vector * vector) * (vector * vector * vector)) :
   (key*commitment*commitment*commitment*commitment)*
   (((int list) * (int list) * (int list)) * (vector * vector * vector) * (vector * vector*vector) *
     (vector * vector*vector) *(vector*vector*vector)*
    (vector*vector*vector)*opening*opening*opening*opening) ={
      var pi1, pi2, pi3, v1, v2, v3, u1, u2, u3, f1, f2, f3;
      var e1, e2, e3, t11, t12, t13, t21, t22, t23, t31, t32, t33;
      var c, c0,c1,c2;
      var r1, r2, r3, r4, key, d, d0, d1, d2;
      
      (* Sample the permutations *)
      pi1 <$ (duniform (allperms (range 0 k)));
      pi2 <$ (duniform (allperms (range 0 k)));
      pi3 <$ (duniform (allperms (range 0 k)));

      (* and the vectors *)
      v1 <$ dvector dR v;
      v2 <$ dvector dR v;
      u1 <$ dvector dR l;
      u2 <$ dvector dR l;
      u3 <$ dvector dR l;
      f1 <$ dvector dR k;
      f2 <$ dvector dR k;
      f3 <$ dvector dR k;

      r1 <$ commit_rand;
      r2 <$ commit_rand;
      r3 <$ commit_rand;
      r4 <$ commit_rand;

      (* and computer v3 *)
      v3 <- h.`3*^v1 + h.`4*^v2;

      (* compute the vectors to commit to *)
      e1 <- h.`2.`1 - (h.`1 *^ (catv w.`2.`1 w.`1.`1));
      e2 <- h.`2.`2 - (h.`1 *^ (catv w.`2.`2 w.`1.`2));
      e3 <- h.`2.`3 - (h.`1 *^ (catv w.`2.`3 w.`1.`3));

      t11 <-  h.`1 *^ (catv u1 v1) + f1;
      t12 <- permVector (- f1) pi1;
      t13 <-  permVector (-(f1 + e1)) pi1;
    
      t21 <-  h.`1 *^ (catv u2 v2) + f2;
      t22 <- permVector (- f2) pi2;
      t23 <-  permVector (-(f2 + e2)) pi2;
    
      t31 <-  h.`1 *^ (catv u3 v3) + f3;
      t32 <- permVector (- f3) pi3;
      t33 <-  permVector (-(f3 + e3)) pi3;

       key <$ keygen;    

      (* make the commitments *)
      (c, d) <- commit key (permToVector pi1,permToVector pi2,permToVector pi3) r1;
      (c0, d0) <- commit key (h.`1 *^ (catv u1 v1) + f1,h.`1 *^ (catv u2 v2) + f2,h.`1 *^ (catv u3 v3) + f3) r2;
      (c1, d1) <- commit key (permVector (- f1) pi1,permVector (- f2) pi2,permVector (- f3) pi3) r3; 
      (c2, d2) <- commit key (permVector (-(f1 + e1)) pi1,permVector (-(f2 + e2)) pi2,permVector (-(f3 + e3)) pi3) r4;
      
        return ((key,c,c0,c1,c2),
        ((pi1,pi2,pi3),(catv u1 v1,catv u2 v2,catv u3 v3),(f1,f2,f3),(t11,t21,t31),(t12,t22,t32),(t13,t23,t33),
        d,d0,d1,d2));  
    }
  
   proc test (h: matrix * (vector *  vector *  vector) * matrix * matrix,
     w: (key*commitment*commitment*commitment*commitment)) : int ={
      var c;
      c <$ (duniform (range 0 3));
      return c;
  }

  proc respond (sw : (matrix * (vector *  vector *  vector) * matrix * matrix )*
    ((vector * vector * vector) * (vector * vector * vector)), ms : (key*commitment*commitment*commitment*commitment)*
    (((int list) * (int list) * (int list)) * (vector * vector*vector) *(vector*vector*vector)*
    (vector*vector*vector)*(vector*vector*vector)*(vector*vector*vector)*opening*opening*opening*opening),  e : int) :
      (((int list) * (int list) * (int list)) * (vector * vector*vector) *(vector*vector*vector)*
      opening*opening*opening*(vector*vector*vector))  ={
      
                           (*perm,      t1,         *)
    return ( if (e=0) then ((ms.`2.`1.`1, ms.`2.`1.`2, ms.`2.`1.`3), (ms.`2.`4.`1, ms.`2.`4.`2, ms.`2.`4.`3),
                            (* t2, opening, v *)
        (ms.`2.`5.`1, ms.`2.`5.`2, ms.`2.`5.`3),ms.`2.`7,ms.`2.`8,ms.`2.`9,(ms.`2.`2.`1,ms.`2.`2.`2,ms.`2.`2.`3)) 
      
                           (*perm,    t0,       t2,       d,        d0           d2 *)
        else if (e=1) then
        ((ms.`2.`1.`1, ms.`2.`1.`2, ms.`2.`1.`3), (ms.`2.`4.`1, ms.`2.`4.`2, ms.`2.`4.`3),
                            (* t2, opening, v *)
          (ms.`2.`6.`1, ms.`2.`6.`2, ms.`2.`6.`3),ms.`2.`7,ms.`2.`8,ms.`2.`10,
          (ms.`2.`2.`1+ (catv sw.`2.`2.`1 sw.`2.`1.`1),ms.`2.`2.`2+ (catv sw.`2.`2.`2 sw.`2.`1.`2),
            ms.`2.`2.`3+ (catv sw.`2.`2.`3 sw.`2.`1.`3)))
        
            else
        (([],[],[]), (ms.`2.`5.`1, ms.`2.`5.`2, ms.`2.`5.`3),
                            (* t2, opening, v *)
        (ms.`2.`6.`1, ms.`2.`6.`2, ms.`2.`6.`3),ms.`2.`9,ms.`2.`9,ms.`2.`10,(zerov (l+v),zerov (l+v),zerov (l+v))));
  }
  
  proc verify (x: matrix * (vector *  vector *  vector) * matrix * matrix,
      m:(key*commitment*commitment*commitment*commitment), e:int ,
      z: (int list*int list*int list)*
    (vector*vector*vector)*(vector*vector*vector)*opening*opening*opening*(vector*vector*vector)) : bool ={
      var resp0, resp1, resp2, resp3, resp4, resp5, d1, d2, d3;
      if (e=0) {
      resp0 <- verify m.`1 (permToVector z.`1.`1,permToVector z.`1.`2,permToVector z.`1.`3) (m.`2, z.`4);
      resp1 <- verify m.`1 z.`2 (m.`3, z.`5);
      resp2 <- verify m.`1  z.`3 (m.`4, z.`6);
      resp3 <- x.`1 *^ z.`7.`1 =  (z.`2.`1 +  permVector  z.`3.`1 (invPerm z.`1.`1)) /\
               x.`1 *^ z.`7.`2 = (z.`2.`2 +  permVector  z.`3.`2 (invPerm z.`1.`2)) /\
               x.`1 *^ z.`7.`3 = (z.`2.`3 +  permVector  z.`3.`3 (invPerm z.`1.`3));
      resp4 <- isPerm z.`1.`1 /\ isPerm z.`1.`2 /\  isPerm z.`1.`3;
      
        d1 <- subv (z.`7.`1) l (l+v);
        d2 <- subv (z.`7.`2) l (l+v);
        d3 <- subv (z.`7.`3) l (l+v);
      resp5 <- d3 = x.`3*^d1 + x.`4*^d2;
    }
    
    else { if (e=1) {
        resp0 <- verify m.`1 (permToVector z.`1.`1,permToVector z.`1.`2,permToVector z.`1.`3) (m.`2, z.`4);
        resp1 <- verify m.`1 z.`2 (m.`3, z.`5);
        resp2 <- verify m.`1 z.`3 (m.`5, z.`6);
        resp3 <- x.`1 *^ z.`7.`1 = (z.`2.`1 +  (permVector  z.`3.`1 (invPerm z.`1.`1)) + x.`2.`1 ) /\
                 x.`1 *^ z.`7.`2 = (z.`2.`2 +  (permVector  z.`3.`2 (invPerm z.`1.`2)) + x.`2.`2 ) /\
                 x.`1 *^ z.`7.`3 = (z.`2.`3 +  (permVector  z.`3.`3 (invPerm z.`1.`3)) + x.`2.`3 );
        d1 <- subv z.`7.`1 l (l+v);
        d2 <- subv z.`7.`2 l (l+v);
        d3 <- subv z.`7.`3 l (l+v);
        resp4 <- d3 = x.`3*^d1 + x.`4*^d2;
        resp5 <- true; }
    
      else { if (e=2) {
        resp0 <- true;
        resp1 <- verify m.`1 z.`2 (m.`4, z.`5); 
        resp2 <- verify m.`1 z.`3 (m.`5, z.`6);
        resp3 <-checkW (z.`2.`1-z.`3.`1) /\ checkW (z.`2.`2-z.`3.`2) /\ checkW (z.`2.`3-z.`3.`3);
        resp4 <- true;
        resp5 <- true;}}}
    
        return resp0 /\ resp1 /\ resp2 /\ resp3 /\ resp4 /\ resp5 /\
        (* statement well foemed *)
        size x.`2.`1 = rows x.`1 /\ size x.`2.`2 = rows x.`1 /\ size x.`2.`3 = rows x.`1 /\ rows x.`1 = k /\ v + l = cols x.`1
        (* response well formed *)
        /\ size z.`2.`1 = k  /\  size z.`2.`2 = k /\ size z.`2.`3 = k /\
        size z.`3.`1 = k  /\  size z.`3.`2 = k /\ size z.`3.`3 = k /\ rows x.`3 = rows x.`4 /\ size z.`7.`1 = l +v /\
         size z.`7.`2 = l +v /\  size z.`7.`3 = l +v;
  } 
}.


module LinearRelAlg : SigmaAlgorithms ={
  proc soundness (h: matrix * (vector *  vector *  vector) * matrix * matrix,
  m : key*commitment*commitment*commitment*commitment,
   z  : (((int list) * (int list) * (int list)) * (vector * vector*vector) *(vector*vector*vector)*
      opening*opening*opening*(vector*vector*vector)),
   z' : (((int list) * (int list) * (int list)) * (vector * vector*vector) *(vector*vector*vector)*
      opening*opening*opening*(vector*vector*vector)),
   z'':  (((int list) * (int list) * (int list)) * (vector * vector*vector) *(vector*vector*vector)*
      opening*opening*opening*(vector*vector*vector))) :
                                                   ((vector*vector*vector)*(vector*vector*vector)) option ={
    var rCatM0, rCatM1, rCatM2;
    rCatM0 <- z'.`7.`1 - z.`7.`1;
    rCatM1 <- z'.`7.`2 - z.`7.`2;
    rCatM2 <- z'.`7.`3 - z.`7.`3;
      return Some ((subv rCatM0 l (l+v), subv rCatM1 l (l+v), subv rCatM2 l (l+v)),
                   (subv rCatM0 0 l,subv rCatM1 0 l,subv rCatM2 0 l));
  }

  proc simulate (h:  matrix * (vector *  vector *  vector) * matrix * matrix,  e: int) :
  (key*commitment*commitment*commitment*commitment)*
  (((int list) * (int list) * (int list)) * (vector * vector*vector) *(vector*vector*vector)*
      opening*opening*opening*(vector*vector*vector)) = {
      var pi1,pi2,pi3,v1,v2,v3,u1,u2,u3,f1,f2,f3,b;
      var t0_0,t0_1,t0_2,t1_0,t1_1,t1_2;
      var key, d, d1, d2, d3, c, c1, c2, c3, r1, r2, r3, r4;
    
      key <$ keygen;
      pi1 <$ (duniform (allperms (range 0 k)));
      pi2 <$ (duniform (allperms (range 0 k)));
      pi3 <$ (duniform (allperms (range 0 k)));
      v1 <$ dvector  dR v;
      v2 <$ dvector dR v;
      u1 <$ dvector dR l;
      u2 <$ dvector dR l;
      u3 <$dvector dR l;
      f1 <$ dvector dR k;
      f2 <$ dvector dR k;
      f3 <$ dvector dR k;
      b <$ chi;

      r1 <$ commit_rand;
      r2 <$ commit_rand;
      r3 <$ commit_rand;
      r4 <$ commit_rand;

      v3 <- h.`3*^v1 + h.`4*^v2;
    
      t0_0 <-  h.`1 *^ (catv u1 v1) + f1;
      t0_1 <-  h.`1 *^ (catv u2 v2) + f2;
      t0_2 <-  h.`1 *^ (catv u3 v3) + f3;
    
      t1_0 <- permVector (- f1) pi1;
      t1_1 <- permVector (- f2) pi2;
      t1_2 <- permVector (- f3) pi3;
    
      (c, d) <- commit key (permToVector pi1, permToVector pi2, permToVector pi3) r1;
      (c1,d1) <- commit key (h.`1 *^ (catv u1 v1) + f1,h.`1 *^ (catv u2 v2) + f2,h.`1 *^ (catv u3 v3) + f3) r2;
      (c2,d2) <- commit key (permVector (- f1) pi1, permVector (- f2) pi2, permVector (- f3) pi3) r3;
      (c3,d3) <- commit key (permVector (f1 + b) pi1,permVector (f2 + b) pi2,permVector (f3 + b) pi3) r4;
      
      if (e=0) {
        (c3, d3) <- commit key (zerov (l+v),zerov (l+v),zerov (l+v)) r4;
      }
      if (e=1) {
        (c1,d1) <- commit key (h.`1 *^ (catv u1 v1) + f1 + h.`2.`1,h.`1 *^ (catv u2 v2) + f2 + h.`2.`2,
            h.`1 *^ (catv u3 v3) + f3 + h.`2.`3) r2;
        (c2,d2) <- commit key (zerov (l+v),zerov (l+v),zerov (l+v)) r3;
        (c3,d3) <- commit key (permVector f1 pi1,permVector f2 pi2,permVector f3 pi3) r4;
      }
      if (e=2) {
        (c,d) <- commit key (zerov (l+v),zerov (l+v),zerov (l+v)) r1;
        (c1,d1) <- commit key (zerov (l+v),zerov (l+v),zerov (l+v)) r2;
      }

      return ( if (e=0) then ((key,c,c1,c2,c3),
          ((pi1,pi2,pi3), (t0_0,t0_1,t0_2), (t1_0,t1_1,t1_2), d, d1, d2,(catv u1 v1,catv u2 v2, catv u3 v3)))
        
        else if (e=1) then ((key,c,c1,c2,c3),

          ((pi1,pi2,pi3),
           (h.`1 *^ (catv u1 v1) + f1 + h.`2.`1,h.`1 *^ (catv u2 v2) + f2 + h.`2.`2,h.`1 *^ (catv u3 v3) + f3 + h.`2.`3),
            (permVector (-f1) pi1, permVector (-f2) pi2,permVector (-f3) pi3), d, d1, d3,(catv u1 v1,catv u2 v2,catv u3 v3))) else
        
        ((key,c,c1,c2,c3),
          (([],[],[]),(t1_0,t1_1,t1_2),(permVector (-f1+b) pi1, permVector (-f2+b) pi2, permVector (-f3+b) pi3),
            d2, d2, d3, (zerov (l+v),zerov (l+v),zerov (l+v)))));
  }
}. 



section Protocol_Security.

  local lemma addvN_genf (a b : vector): size a = size b => a = a -b + b.
    smt(@MLWE.M).
  qed.

 local lemma addvN_genl (a b : vector): size a = size b => a = a +b - b.
    smt(@MLWE.M).
  qed.  

  local lemma inImageHelp m (u v : vector) f pi :
  pi \in duniform (allperms (range 0 k)) =>
  f \in dvector dR k =>
  rows m = k =>
  m *^ (u || v) =
  m *^ (u || v) + f +
  permVector (permVector (-f) pi) (invPerm pi).
proof.
  move => h0 h1 h2. have : isPerm pi. smt(@Distr @List @Perms). move => g0. have : size f = k.
  smt(@Distr @MLWE.M gt0_k). move => g1. rewrite permVectorInv. smt(@Distr @List @Perms). smt(@List @Distr @MLWE.M @Int).
  rewrite -addvA. rewrite addvN. rewrite lin_addv0. smt(@MLWE.M). smt(@MLWE.M).
qed.

 (* We also use this lemma for the linear relation check *)
 local lemma inImageHelpSub m (u v : vector) f (c w1 w2 : vector) :
   f \in dvector dR k =>
   rows m = k =>  
   size c = k =>  
   m *^ (u || v) + f - (f + (c - m *^ (w2 || w1))) + c = m*^ ((u || v) + (w2 || w1)).
  proof.    
    move => ? ? ?. rewrite mulmxvDr. rewrite -addvA. rewrite -addvA. congr. rewrite oppvD.
    rewrite oppvD. rewrite !addvA.  rewrite addvN. rewrite lin_add0v. smt(@MLWE.M). rewrite oppvK.
    rewrite addvC. rewrite addvA. rewrite addvN. smt(@MLWE.M). 
  qed.
  
 local lemma inImageHelp2 m (u v : vector) f pi (c w2 w1 : vector) :
  pi \in duniform (allperms (range 0 k)) =>
  f \in dvector dR k =>
  rows m = k =>
  size c = k =>  
   m *^ ((u || v) + (w2 || w1)) = m *^ (u || v) + f +
   permVector (permVector (- (f + (c - m *^ (w2 || w1)))) pi) (invPerm pi) +c .
proof.
  move => h0 h1 h2 h3. have : isPerm pi. smt(@Distr @List @Perms). move => g0. have : size f = k.
  smt(@Distr @MLWE.M gt0_k). move => g1. 
  rewrite permVectorInv. smt(@Distr @List @Perms). smt(@List @Distr @MLWE.M @Int).
  rewrite inImageHelpSub; trivial.  
qed.


  local lemma checkWHelp (f c u v: vector) pi A :  pi \in duniform (allperms (range 0 k))=> size f = k => 
     size c = k => rows A = k => checkW (c - A *^ (u || v)) =>
     checkW (permVector (-f) pi - permVector (- (f + (c - A *^ (u || v)))) pi).
  proof.
    move => h0 h1 h2 h3 h4. have : isPerm pi. smt(@Distr @Perms @List). move => h5.
    rewrite permVectorOp; trivial. rewrite permVectorAdd; trivial. smt(@MLWE.M @List). rewrite size_oppv.
    rewrite size_oppv. smt(@MLWE.M @List). rewrite -checkWPerm; trivial. rewrite oppvK. rewrite addvA. rewrite (addvC _ f).
    rewrite addvN. rewrite addvC. rewrite lin_addv0. smt(@MLWE.M).  smt(@MLWE.M). rewrite oppvK. rewrite addvA. rewrite (addvC _ f).
    rewrite addvN. rewrite addvC. rewrite lin_addv0. smt(@MLWE.M).  smt(@MLWE.M).
  qed. 

  local lemma absurd_distr e b :
    e \in duniform (range 0 3) => e <> 0 => e <> 1 => e <> 2 => b.  
  proof.
    move => h3 e0 e1 e2. smt(@Distr).
  qed.
      
  lemma LinerRelProt_Completeness s w' &m:
  R s w' =>
  Pr[Completeness(LinearRelProt).main(s, w') @ &m  : res] = 1%r.
  proof.
  move => @/R. move => h. byphoare (: arg = (s, w') ==> res) => //.
    conseq (: true ==> true: =1%r)(: arg = (s, w') ==> res). auto.
    (* correctness *)
    proc. inline *. auto. progress.
  
    (* case 0 *)(* verify commitment *)
    smt(commit_verify_correct). smt(commit_verify_correct). smt(commit_verify_correct).
    (* in images *)
    apply inImageHelp; trivial. smt(). apply inImageHelp; trivial. smt(). apply inImageHelp; trivial. smt().
    (* perms *)
    apply isPermSimp; trivial. apply isPermSimp; trivial. apply isPermSimp; trivial.
    (*linear relation *)
    rewrite subv_catvCr_ins; trivial.  smt(@MLWE.M). rewrite subv_catvCr_inin; trivial. rewrite subv_catvCr_inin; trivial. 
  
    (* misc *)
    smt(). smt(). smt(). smt(). smt(). smt(@MLWE.M). smt(@MLWE.M).  smt(@MLWE.M).
    apply permVectorSize. apply isPermSimp. trivial. apply permVectorSize. apply isPermSimp. trivial. 
    apply permVectorSize. apply isPermSimp. trivial. 
    smt(). smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M).

    (* case 1 *)(* verify commitment *)
    smt(commit_verify_correct). smt(commit_verify_correct). smt(commit_verify_correct). 
    (* in images *)
    apply inImageHelp2; trivial. smt(). smt(). apply inImageHelp2; trivial. smt(). smt().
    apply inImageHelp2; trivial. smt(). smt(). 
    (* linear realtion *)
    rewrite addv_catv. smt(@Distr @MLWE.M gt0_l). rewrite subv_catvCr_ss. smt(@MLWE.M).  smt(@MLWE.M).
    rewrite addv_catv. smt(@Distr @MLWE.M gt0_l). rewrite subv_catvCr_ss. smt(@MLWE.M).  smt(@MLWE.M).
    rewrite addv_catv. smt(@Distr @MLWE.M gt0_l). rewrite subv_catvCr_ss. smt(@MLWE.M).  smt(@MLWE.M).
    rewrite h.  rewrite mulmxvDr. rewrite mulmxvDr. have : forall (a b c d : vector),
    a = c => b = d => a + b = c + d. smt(). move => H17. rewrite -addvA. rewrite -addvA. apply H17.  trivial.
    rewrite addvC. rewrite -addvA. apply H17. trivial. smt(@MLWE.M). 
    (* misc *)
    smt(). smt(). smt(). smt(). smt(). smt(@MLWE.M). smt(@MLWE.M).  smt(@MLWE.M).
    apply permVectorSize. apply isPermSimp. trivial. apply permVectorSize. apply isPermSimp. trivial. 
    apply permVectorSize. apply isPermSimp. trivial. smt().  smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M).

    (* case 2 *)(* verify commitment *)
    smt(commit_verify_correct).  smt(commit_verify_correct).  
    (* check W -  1 *)
    apply checkWHelp; trivial. smt(@Distr @MLWE.M). smt(). smt(). smt().
    (* 2 *)
    apply checkWHelp; trivial. smt(@Distr @MLWE.M). smt(). smt(). smt().
    (* 3 *)
    apply checkWHelp; trivial. smt(@Distr @MLWE.M). smt(). smt(). smt().
  
    (* Misc *)
    smt(). smt(). smt(). smt(). smt(). apply permVectorSize. apply isPermSimp. trivial. 
    apply permVectorSize. apply isPermSimp. trivial. apply permVectorSize. apply isPermSimp. trivial. 
    apply permVectorSize. apply isPermSimp. trivial. apply permVectorSize. apply isPermSimp. trivial. 
    apply permVectorSize. apply isPermSimp. trivial.  smt(). smt(). smt(). smt().
    
    (* dumb case *)
    apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial.
    apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial.
    apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial.
    apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial.
    apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial.
    apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial.
    apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial. apply (absurd_distr c30); trivial.
    (* termination *)
    proc. inline *. auto. progress. apply duniform_ll.
    have : forall (l : int list list), (exists (x : int list), x \in l) => l <> [].
    move => l h1. elim h1. move => x h1. smt(@List). move => h1. apply h1. exists (range 0 k). smt(@List @Perms).
    smt(dR_ll @MLWE.M). smt(dR_ll @MLWE.M). smt(dR_ll @MLWE.M). apply commit_rand_ll. apply keygen_ll.  smt(@Int @Distr @List).
  qed. 

  local lemma inImageSound A (t u w u' w' : vector) pi (c : vector) :
      isPerm pi =>
      size u' = k =>
      size w' = k =>
      size t = k =>
      size c = k =>
      A *^ u = (t + permVector u' (invPerm pi)) =>
      A *^ w = (t + permVector w' (invPerm pi) + c) =>
      checkW (u' - w') =>
      checkW (c - A *^ (u - w)).
  proof.
    move => h1 h2 h3 h4 h5 h6 h7 h8. rewrite mulmxvDr. rewrite (bRing w). rewrite h6. rewrite h7.
    have : (t + permVector u' (invPerm pi) + (t + permVector w' (invPerm pi) + c)) = (c + permVector ((-u') + w') (invPerm pi)).
    have : forall (a b c d : vector), a + b = d => a + (b + c) = c + d.  smt(@MLWE.M). move => h'. apply h'.
    rewrite (addvC _ (permVector w' (invPerm pi))). rewrite -addvA. rewrite (addvA _ _ t). rewrite permVectorAdd.
    apply invPermPerm. apply h1. rewrite h2. apply isPerm_size_k. apply invPermPerm. trivial.
    rewrite h3. apply isPerm_size_k. apply invPermPerm. trivial.  rewrite (bRing u').
    pose q := (permVector (u' + w') (invPerm pi) + t). rewrite -(bRing t). move => @/q. rewrite addvC. rewrite -addvA.
    rewrite addvN. rewrite lin_addv0. rewrite permVectorSize. apply invPermPerm. smt(@List @Distr @Perms). trivial. trivial.
     move => h'. rewrite h'.
    rewrite oppvD. rewrite addvA. rewrite addvN. rewrite lin_add0v. rewrite size_oppv. rewrite permVectorSize. apply invPermPerm.
    smt(@List @Distr @Perms). trivial. trivial. rewrite bRing. rewrite -checkWPerm.  apply invPermPerm. smt(@List @Distr @Perms).
    rewrite bRing. rewrite -(bRing w'). smt(@M). smt(bRing).
  qed.

  local lemma sound_open A (c u w u' w' t : vector) pi :
      isPerm pi =>
      l + v = cols A =>
      size c = k =>
      size u = l + v =>
      size w = l + v =>
      size u' = k =>
      size w' = k =>
      size t = k =>
      A *^ u = (t + permVector u' (invPerm pi)) =>
      A *^ w = (t + permVector w' (invPerm pi) + c) =>
      checkW (u' - w') =>
      checkW (c - A *^ (subv (w - u) 0 l || subv (w - u) l (l + v))).
  proof.
    move => h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11. rewrite catv_subvC_gen. smt(@MLWE.M). smt(@MLWE.M gt0_l gt0_v). 
    (* Showing that image actutally exists *)
    rewrite (addvC w). rewrite (bRing u). rewrite -(bRing w). apply (inImageSound _ t _ _ u' w' pi _); trivial.
  qed. 
    
  (* Binding is perfect *)
  lemma LinearRelProt_Sound (F <: SigmaFaker)  &m:
    hoare[SpecialSoundnessExperiment(LinearRelProt, LinearRelAlg, F).main : true ==> res].
  proof.
    proc. inline *. auto. call(_:true). auto. move => _ [[A [y1 y2 y3] X1 X2] [k c c1 c2 c3]].
    move => [[e0pi0 e0pi1 e0pi2] [e0t00 e0t10 e0t20] [e0t01 e0t11 e0t21] e0d0 e0d1 e0d2 [e0v0 e01 e0v2]].
    move => [[e1pi0 e1pi1 e1pi2] [e1t00 e1t10 e1t20] [e1t01 e1t11 e1t21] e1d0 e1d1 e1d2 [e1v0 e1v1 e1v2]].
    move => [[e2pi0 e2pi1 e2pi2] [e2t00 e2t10 e2t20] [e2t01 e2t11 e2t21] e2d0 e2d1 e2d2 [e2v0 e2v1 e2v2]].
  
      simplify. move => h. elim h => h0 h. elim h => h1 h2. elim h0 => h00 h0.  elim h1 => h10 h1. elim h2 => h20 h2.
  
    (* Using commitments and clear *)
    have : (e0pi0, e0pi1, e0pi2) = (e1pi0, e1pi1, e1pi2). apply permToVectorInj3. apply (commit_verify_sound k  _ _ c e0d0 e1d0).
    smt(). smt().  move => h. elim h => ->> ->> ->>.  (* Permutation Commitments done *) clear h10 h00.
    elim h1 => h10 h1. elim h0 => h00 h0.
    have : (e0t00,e0t10,e0t20) = (e1t00,e1t10,e1t20). apply (commit_verify_sound k  _ _ c1 e0d1 e1d1). smt(). smt(). move => h.
    elim h => ->>. clear h00 h10.  elim h2 => h21 h2. elim h1 => h10 h1. elim h0 => h00 h0.
    have : (e0t01, e0t11, e0t21) = (e2t00, e2t10, e2t20). apply (commit_verify_sound k  _ _ c2 e0d2 e2d1). smt(). smt().
    move => h. elim h => ->> ->> ->>. clear h00. clear h20.
    have : (e1t01, e1t11, e1t21) = (e2t01, e2t11, e2t21). apply (commit_verify_sound k  _ _ c3 e1d2 e2d2). smt(). smt().
    move => h. elim h => ->> ->> ->>. clear h10 h21.
    (* commitments done *) clear c c1 c2 c3 e0d0 e0d1 e0d2 e1d0 e1d1 e1d2 e2d0 e2d1 e2d2.
    elim h2 => h2 h20. elim h0 => h0 h00. elim h1 => h1 h10. elim h00. progress; simplify.
  
    (* Show we have an opening for the first commitment *)
    elim h10 => [k0 [k1 [k2 [k3 [k4 [k5 [k6 [k7 [k8 [k9 [k10 [k11 [k12 [k13 k14]]]]]]]]]]]]]].
    elim h20 => [j0 [j1 [j2 [j3 [j4 [j5 [j6 [j7 [j8 [j9 [j10 [j11 [j12 [j13 j14]]]]]]]]]]]]]].
    elim h0 => [l0 [l1 l2]].
    elim h1 => [d0 [d1 d2]].
    elim h2 => [s0 [s1 s2]].
      apply (sound_open _ _ _ _ e2t00 e2t01 e1t00 e1pi0); trivial. smt(). smt(). 
    (* Show we have an opening for the second commitment *)
    elim h10 => [k0 [k1 [k2 [k3 [k4 [k5 [k6 [k7 [k8 [k9 [k10 [k11 [k12 [k13 [k14 k15]]]]]]]]]]]]]]].
    elim h20 => [j0 [j1 [j2 [j3 [j4 [j5 [j6 [j7 [j8 [j9 [j10 [j11 [j12 [j13 j14]]]]]]]]]]]]]].
    elim h0 => [l0 [l1 l2]].
    elim h1 => [d0 [d1 d2]].
    elim h2 => [s0 [s1 s2]].
    apply (sound_open _ _ _ _ e2t10 e2t11 e1t10 e1pi1); trivial. smt(). smt(). 
    (* Show we have an opening for the third commitment *)
    elim h10 => [k0 [k1 [k2 [k3 [k4 [k5 [k6 [k7 [k8 [k9 [k10 [k11 [k12 [k13 [k14 k15]]]]]]]]]]]]]]].
    elim h20 => [j0 [j1 [j2 [j3 [j4 [j5 [j6 [j7 [j8 [j9 [j10 [j11 [j12 [j13 j14]]]]]]]]]]]]]].
    elim h0 => [l0 [l1 l2]].
    elim h1 => [d0 [d1 d2]].
    elim h2 => [s0 [s1 s2]].
    apply (sound_open _ _ _ _ e2t20 e2t21 e1t20 e1pi2); trivial. smt(). smt().

    (* Linear relation *)
    elim h10 => h10 h100. rewrite subv_addv. smt(@MLWE.M). rewrite bRing. rewrite H2. rewrite h10.
    rewrite subv_addv. smt(@MLWE.M). rewrite subv_addv. smt(@MLWE.M). rewrite mulmxvDr. rewrite mulmxvDr.
    rewrite -!addvA. congr. rewrite addvC. rewrite !bRing. rewrite -!addvA. congr. apply addvC.
    (* Remaing errors *)
    smt(). smt(). smt(). smt(). smt(). smt(). smt(gt0_l). smt(gt0_l gt0_v). smt(gt0_l). smt(gt0_l gt0_v). smt(gt0_l).
    smt(gt0_l gt0_v). 
  qed. 

  local lemma t1_simp A (u v f c r m: vector):
     size u = size r => cols A = size r + size m => size c = rows A =>
     A *^ (u || v) + f + c =
     A *^ (u -r || v - m) + (f - (c - A *^ (r || m))).
      proof.
        move => h0 h1 h2. rewrite -addv_catv. smt(@MLWE.M). rewrite mulmxvDr. rewrite -!addvA.
        congr. rewrite (addvC (A *^ _)). rewrite bRing. rewrite bRing.
        rewrite -!addvA. rewrite -mulmxvDr. rewrite addv_catv. smt(@MLWE.M). rewrite !addvN.
        have : forall a, a = zerov (cols A) =>  A *^ (a) = zerov (rows A). smt(@MLWE.M).
        move => h'. rewrite h'. apply eq_vectorP. split. smt(@MLWE.M). move => i hi. smt(@MLWE.M).
        smt(@MLWE.M).
    qed.

    local lemma t1_3_simp (M1 M2 : matrix) (v v' m m' : vector) :
      M1 *^ (v - m) + M2 *^ (v' -m') = (M1 *^v + M2 *^ v') - (M1 *^m + M2 *^ m').
    proof.
      rewrite !mulmxvDr. rewrite -!addvA. congr.  rewrite !bRing. rewrite !addvA. congr.
      smt(@MLWE.M).
  qed.

  local lemma t2_simp (f b v : vector) (pi : int list)  :
    size f = k =>
    size b = k =>
    size v = k =>  
    isPerm pi =>
    weight b = weight v =>  
    permVector (f + b) pi =
    permVector (permVector f (invPerm  (findPermEq b v)) +  v) (composePerm (findPermEq b v) pi).
  proof.
    move => h0 h1 h2 h3 h5. have : size pi = k. smt(@Perms @List gt0_k). move => h4. rewrite -permVectorAdd.
    trivial. smt(). smt(). rewrite -permVectorAdd. apply composePermPerm. apply findPermChecks. trivial. rewrite permVectorSize.
    apply invPermPerm. apply findPermChecks. rewrite size_map. trivial. rewrite size_map. smt().
    rewrite composePermCorrect; trivial. apply invPermPerm. apply findPermChecks. apply composePermPerm. apply findPermChecks.
    trivial.  rewrite -composePermA. apply invPermPerm. apply findPermChecks. apply findPermChecks. trivial.
    rewrite composePermNeg. apply findPermChecks. rewrite composePermID. trivial. congr.
    rewrite -composePermCorrect; trivial. apply findPermChecks. rewrite -findPermCorr.  apply permEqWeight; trivial. smt(). trivial.
 qed.

  local lemma t3_e2 (f : vector) (s1: matrix) (s2 :vector) (w1 w2 : vector) pi bW : isPerm pi => size f = k => size s2 = k =>
         rows s1 = k => arePermEq (s2 + s1 *^ (w2 || w1)) bW => size bW = k =>
      permVector ((f) + (s2 + s1 *^ (w2 || w1))) pi =
      permVector (permVector f
        (invPerm (findPermEq (s2 + s1 *^ (w2 || w1)) bW)) + bW)
      (composePerm (findPermEq (s2 + s1 *^ (w2 || w1)) bW) pi).
  proof.      
    move => isPerm size_f size_s2 size_s1 permEq size_bW. apply t2_simp; trivial. smt(@List). elim permEq => pi' h.
    elim h => h h'. rewrite h'. rewrite eq_sym. apply weightPerm. smt(). trivial. 
  qed.

   (* The reduction from the ZK adversary to the commitment scheme adversary *)
  module U (D : Decider) : Unhider = {
    var ck : key
    var pi1, pi2, pi3 : int list
    var v1, v2, u1, u2, u3 : vector
    var f1, f2, f3 : vector
    var bW : vector
    
    proc choose(x:key,a:(matrix * (vector*vector*vector) * matrix * matrix)*
    ((vector * vector * vector) *(vector*vector*vector))*int) = {
      var e1, e2, e3, v3;
      
      pi1 <$ (duniform (allperms (range 0 k)));
      pi2 <$ (duniform (allperms (range 0 k)));
      pi3 <$ (duniform (allperms (range 0 k)));
      v1 <$ dvector  dR v;
      v2 <$ dvector dR v;
      u1 <$ dvector dR l;
      u2 <$ dvector dR l;
      u3 <$dvector dR l;
      f1 <$ dvector dR k;
      f2 <$ dvector dR k;
      f3 <$ dvector dR k;
      bW <$ chi;

      v3 <- a.`1.`3*^v1 + a.`1.`4*^v2;

      ck <- x;

      e1 <- a.`1.`2.`1 - (a.`1.`1 *^ (catv a.`2.`2.`1 a.`2.`1.`1));
      e2 <- a.`1.`2.`2 - (a.`1.`1 *^ (catv a.`2.`2.`2 a.`2.`1.`2));
      e3 <- a.`1.`2.`3 - (a.`1.`1 *^ (catv a.`2.`2.`3 a.`2.`1.`3));
      
      return (((zerov (l+v), zerov (l+v), zerov (l+v)),(zerov (l+v), zerov (l+v), zerov (l+v))),
        (if (a.`3 = 2) then
          (permToVector (composePerm (invPerm (findPermEq e1 bW)) pi1),permToVector (composePerm (invPerm (findPermEq e2 bW)) pi2),
            permToVector (composePerm (invPerm (findPermEq e3 bW)) pi3)) else
          (permVector (-(f1 + e1)) pi1,permVector (-(f2 + e2)) pi2,permVector (-(f3 + e3)) pi3),
        if (a.`3 = 1) then  (permVector (-f1 + (a.`1.`2.`1 - a.`1.`1 *^ (a.`2.`2.`1 || a.`2.`1.`1))) pi1,
            permVector (-f2 + (a.`1.`2.`2 - a.`1.`1 *^ (a.`2.`2.`2 || a.`2.`1.`2))) pi2,
            permVector (-f3 + (a.`1.`2.`3 - a.`1.`1 *^ (a.`2.`2.`3 || a.`2.`1.`3))) pi3)
        else (a.`1.`1 *^ (catv u1 v1) + (permVector f1  (findPermEq e1 bW)),
              a.`1.`1 *^ (catv u2 v2) + (permVector f2  (findPermEq e2 bW)),
              a.`1.`1 *^ (catv u3 v3) + (permVector f3  (findPermEq e3 bW)))));
    }

    proc guess(c:commitment*commitment,a:(matrix * (vector*vector*vector) * matrix * matrix)*
    ((vector * vector * vector) *(vector*vector*vector))*int) = {
      var c0,c1,c2,c3,d0,d1,d2,d3, r1, r2, r3, r4, b, com, resp, v3;

      r1 <$ commit_rand;
      r2 <$ commit_rand;
      r3 <$ commit_rand;
      r4 <$ commit_rand;

      v3 <- a.`1.`3*^v1 + a.`1.`4*^v2;
      
      (c0, d0) <- commit ck (permToVector pi1,permToVector pi2,permToVector pi3) r1;
      (c1, d1) <- if (a.`3=1) then
        commit ck (a.`1.`1 *^ (catv u1 v1) + f1 + a.`1.`2.`1,
                   a.`1.`1 *^ (catv u2 v2) + f2 + a.`1.`2.`2,
                   a.`1.`1 *^ (catv u3 v3) + f3 + a.`1.`2.`3) r2 else
         commit ck (a.`1.`1 *^ (catv u1 v1) + f1, a.`1.`1 *^ (catv u2 v2) + f2, a.`1.`1 *^ (catv u3 v3) + f3) r2;

      (c2,d2) <- commit ck (permVector (- f1) pi1, permVector (- f2) pi2, permVector (- f3) pi3) r3;
      (c3,d3) <- if(a.`3 = 1) then commit ck (permVector f1 pi1, permVector f2 pi2, permVector f3 pi3) r4 else
                                   commit ck (permVector (f1 + bW) pi1, permVector (f2 + bW) pi2, permVector (f3 + bW) pi3) r4;

      com <- if (a.`3 = 0) then (ck,c0,c1,c2,c.`1) else (
        if (a.`3 = 1) then (ck,c0,c1,c.`2,c3) else (ck,c.`1,c.`2,c2,c3));

      resp <- if (a.`3=0) then ((pi1,pi2,pi3),
        (a.`1.`1 *^ (catv u1 v1) + f1, a.`1.`1 *^ (catv u2 v2) + f2, a.`1.`1 *^ (catv u3 v3) + f3),
        (permVector (- f1) pi1, permVector (- f2) pi2, permVector (- f3) pi3), d0, d1,  d2, (catv u1 v1, catv u2 v2, catv u3 v3)) else 
        (if (a.`3=1)then
          ((pi1, pi2, pi3),(a.`1.`1 *^ (catv u1 v1) + f1 + a.`1.`2.`1,
          a.`1.`1 *^ (catv u2 v2) + f2 + a.`1.`2.`2, a.`1.`1 *^ (catv u3 v3) + f3 + a.`1.`2.`3),
            (permVector (- f1) pi1, permVector (- f2) pi2, (permVector (- f3) pi3)), d0, d1,  d3,
        (catv u1 v1, catv u2 v2, catv u3 v3)) else 
      (([],[],[]), (permVector (-f1) pi1, permVector (-f2) pi2, permVector (-f3) pi3),
        (permVector (-(f1+ bW)) pi1, permVector (-(f2+ bW)) pi2, permVector (-(f3+ bW)) pi3), d2, d2, d3,
          (zerov (l+v), zerov (l+v), zerov (l+v))));  
      
      b <@ D.distinguish(a.`1, com,a.`3,resp);
      return b;
    }
  }.

  declare module D <: Decider {-U.ck, -U.f1, -U.f2, -U.f3, -U.pi1, -U.pi2, -U.pi3, -U.u1, -U.u2, -U.u3, -U.v1, -U.v2, -U.bW}.

  local lemma Real_GB_0 s w e &m :
        e \in range 0 3 =>
      Pr[SHVZK(LinearRelProt, LinearRelAlg, D).simulate(s,e) @ &m : res] =
        Pr[HidingExperimentL(U(D)).main((s,w,e)) @ &m : res].
  proof.     
    move => Ran.
    case(e = 0) => he1. subst. byequiv. proc. inline *. wp. call(_:true). wp. swap{2} [28..31] -6. wp. rnd{2}. rnd. rnd{2}.
    auto. progress. apply commit_rand_ll. auto. auto.
    (* challenge case 1 *)
    case(e = 1) => he2. subst. byequiv. proc. inline *. wp. call(_:true). wp. swap{2} [28..31] -6. wp. swap{2} 27 - 3. rnd{2}.
    rnd. rnd{2}.  auto. progress. apply commit_rand_ll. auto. auto.
    (* challenge case 2 *)
    have : (e =2). smt(@List). move => he3. subst. byequiv. proc. inline *. wp. call(_:true). wp. 
    swap{2} [28..31] -4. wp. rnd. rnd. rnd{2}. rnd{2}. auto. progress. apply commit_rand_ll.
    rewrite !bRing. trivial. rewrite !bRing. trivial. rewrite !bRing. trivial. auto. auto. 
  qed.
  
  local lemma Real_GB_1 s w e &m :
        R s w =>
        e \in range 0 3 =>
        Pr[SHVZK(LinearRelProt, LinearRelAlg, D).real(s,w,e) @ &m : res] =
        Pr[HidingExperimentR(U(D)).main((s,w,e)) @ &m : res].
    proof.
      move => @/R Rel Ran.
      (* case 0 *)
      case (e = 0) => h0. rewrite h0.  byequiv => //. proc. inline *. wp. call(_:true). inline *. wp.
      swap{1} 31 -30. wp. swap{2} [28..31] -6. wp. rnd{2}. rnd. rnd{2}. rnd. rnd. rnd. wp. rnd{2}. auto. progress.
      apply chi_ll. apply commit_rand_ll.

      (* case 1 *)
      case (e =1) => h1. rewrite h1. byequiv => //. proc. inline *. wp. call(_:true). wp.
      swap{1} 31 -30. wp. swap{2} [28..31] -6. wp. swap{2} 27 - 3. rnd{2}. rnd.  rnd{2}.  rnd.  rnd. rnd. wp. rnd{2}.
     (* sample f *)  rnd(fun (f : vector), f - (s{2}.`2.`3 - s{2}.`1 *^ (w{2}.`2.`3 || w{2}.`1.`3)))
   (fun (f : vector), f + (s{2}.`2.`3 - s{2}.`1 *^ (w{2}.`2.`3 || w{2}.`1.`3))).
   
     rnd(fun (f : vector), f - (s{2}.`2.`2 - s{2}.`1 *^ (w{2}.`2.`2 || w{2}.`1.`2)))
   (fun (f : vector), f + (s{2}.`2.`2 - s{2}.`1 *^ (w{2}.`2.`2 || w{2}.`1.`2))). wp.
   
     rnd(fun (f : vector), f - (s{2}.`2.`1 - s{2}.`1 *^ (w{2}.`2.`1 || w{2}.`1.`1)))
     (fun (f : vector), f + (s{2}.`2.`1 - s{2}.`1 *^ (w{2}.`2.`1 || w{2}.`1.`1))).
     (* sample u (s) *)
     rnd(fun b, b - w{2}.`2.`3)(fun b, b +  w{2}.`2.`3).
     rnd(fun b, b - w{2}.`2.`2)(fun b, b +  w{2}.`2.`2).
     rnd(fun b, b - w{2}.`2.`1)(fun b, b +  w{2}.`2.`1).
     (* sample vs *)
     rnd(fun b, b - w{2}.`1.`2)(fun b, b +  w{2}.`1.`2).
     rnd(fun b, b - w{2}.`1.`1)(fun b, b +  w{2}.`1.`1). 
     
     (* smaple pi *) rnd. rnd. rnd.
     auto. progress.
     (* sampling correct *)  rewrite -addvA. rewrite addvN. rewrite lin_addv0. smt(@Distr @MLWE.M).
       trivial.  apply dRmu1ins. apply gt0_v. trivial. smt(). apply dRin. smt(@MLWE.M). smt(@MLWE.M).
    smt(@MLWE.M). apply dRmu1ins.  apply gt0_v. trivial. smt(). apply dRin. smt(@MLWE.M). smt(@MLWE.M). rewrite -addvA.
       rewrite addvN. rewrite lin_addv0. smt(@Distr @MLWE.M).
       trivial.   apply dRmu1ins. apply gt0_l. trivial. smt(). apply dRin. smt(@MLWE.M).
       smt(@MLWE.M). smt(@MLWE.M). apply dRmu1ins.  apply gt0_l. trivial. smt(). apply dRin. smt(@MLWE.M). smt(@MLWE.M).
       rewrite -addvA. rewrite addvN. rewrite lin_addv0. smt(@Distr @MLWE.M). trivial. apply dRmu1ins.
       apply gt0_l. trivial. smt(). apply dRin. smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M). apply dRmu1ins.
       apply gt0_k. trivial. smt(@MLWE.M).  apply dRin. smt(@MLWE.M). apply addvN_genf. smt(@MLWE.M). apply addvN_genl.
       smt(@MLWE.M). apply dRmu1ins. apply gt0_k. trivial. smt(@MLWE.M). apply dRin. smt(@MLWE.M). apply addvN_genf.
       smt(@MLWE.M). apply addvN_genl.  smt(@MLWE.M).  apply dRmu1ins. apply gt0_k. trivial. smt(@MLWE.M). apply dRin.
       smt(@MLWE.M). apply addvN_genf. smt(@MLWE.M). apply chi_ll.
     
     (* dealing with commitment hiding *) apply commit_rand_ll.
     (* message in c1 *) rewrite -(t1_simp h{1}.`1 u1L v1L). smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M).
       rewrite -t1_simp.  smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M). elim Rel => [h2 [h3 [h4 [h5 Rel]]]].  rewrite  t1_3_simp.
       rewrite -h5. rewrite -t1_simp.  smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M). rewrite -bRing_cancel. smt(@MLWE.M).
       rewrite -bRing_cancel. smt(@MLWE.M).  rewrite -bRing_cancel. smt(@MLWE.M). trivial.
     (* message in c3 *) rewrite !bRing.  rewrite -bRing_cancel. smt(@MLWE.M).  rewrite -bRing_cancel. smt(@MLWE.M).
       rewrite -bRing_cancel. smt(@MLWE.M). trivial.
       (* message in c4 *) rewrite !bRing. trivial.
       (* t1 openings *) rewrite -(t1_simp h{1}.`1 u1L v1L).  smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M). apply bRing_cancel.
       smt(@MLWE.M).  rewrite -(t1_simp h{1}.`1 u2L v2L).  smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M). apply bRing_cancel.
       smt(@MLWE.M). rewrite t1_3_simp.  elim Rel => [h2 [h3 [h4 [h5 Rel]]]]. rewrite -h5.
       rewrite -(t1_simp h{1}.`1 u3L _).  smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M). apply bRing_cancel. smt(@MLWE.M).
       trivial. rewrite !bRing. trivial. rewrite !bRing. trivial. rewrite !bRing. trivial.
     (* opening in c1 *)
      rewrite -(t1_simp h{1}.`1 u1L v1L). smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M).
       rewrite -t1_simp.  smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M). elim Rel => [h2 [h3 [h4 [h5 Rel]]]].  rewrite  t1_3_simp.
       rewrite -h5. rewrite -t1_simp.  smt(@MLWE.M). smt(@MLWE.M). smt(@MLWE.M). rewrite -bRing_cancel. smt(@MLWE.M).
       rewrite -bRing_cancel. smt(@MLWE.M).  rewrite -bRing_cancel. smt(@MLWE.M). trivial.
       (* openings in c3 *) rewrite !bRing.  trivial. smt(@MLWE.M bRing). smt(@MLWE.M bRing). rewrite t1_3_simp.
     elim Rel => [h2 [h3 [h4 [h5 Rel]]]]. rewrite -h5. smt(@MLWE.M bRing).

      (* case 2 *)
     have : e = 2. smt(@List). move => h2. rewrite h2.
     byequiv => //. proc. inline *. wp. call(_:true). wp. swap{1} 31 -30.
       swap{2} [30..31] -6. wp. rnd{2}. rnd{2}. wp. rnd. rnd. rnd. rnd. wp. swap{2} 15 -11.  
     (* Sample f *) rnd(fun (f : vector),
     permVector (f) (invPerm (findPermEq (- (s{2}.`2.`3 - s{2}.`1 *^ (w{2}.`2.`3 || w{2}.`1.`3))) U.bW{2})))
     (fun (f:vector),
       permVector (f) (findPermEq (- (s{2}.`2.`3 - s{2}.`1 *^ (w{2}.`2.`3 || w{2}.`1.`3))) U.bW{2})).
     
     rnd (fun (f : vector), permVector (f) (invPerm (findPermEq
           (- (s{2}.`2.`2 - s{2}.`1 *^ (w{2}.`2.`2 || w{2}.`1.`2)))  U.bW{2})))
     (fun (f:vector),
       permVector (f) (findPermEq (- (s{2}.`2.`2 - s{2}.`1 *^ (w{2}.`2.`2 || w{2}.`1.`2))) U.bW{2})).
     
      rnd (fun (f : vector), permVector (f) (invPerm (findPermEq 
           (- (s{2}.`2.`1 - s{2}.`1 *^ (w{2}.`2.`1 || w{2}.`1.`1))) U.bW{2})))
     (fun (f:vector),
       permVector (f) (findPermEq (- (s{2}.`2.`1 - s{2}.`1 *^ (w{2}.`2.`1 || w{2}.`1.`1))) U.bW{2})).

     (* Sample vBold *) rnd. rnd. rnd. rnd. rnd.
     (* Sample pi *) rnd(fun pi, composePerm 
       (findPermEq (-(s{2}.`2.`3 - s{2}.`1 *^ (w{1}.`2.`3 || w{1}.`1.`3))) U.bW{2}) pi{2})
     (fun pi, (composePerm (invPerm
           (findPermEq (-(s{2}.`2.`3 - s{2}.`1 *^ (w{1}.`2.`3 || w{1}.`1.`3))) U.bW{2})) pi{2})).
      rnd(fun pi, composePerm
       (findPermEq (-(s{2}.`2.`2 - s{2}.`1 *^ (w{1}.`2.`2 || w{1}.`1.`2))) U.bW{2}) pi{2})
     (fun pi, (composePerm(invPerm
           (findPermEq (-(s{2}.`2.`2 - s{2}.`1 *^ (w{1}.`2.`2 || w{1}.`1.`2))) U.bW{2}))  pi{2} )).
      rnd(fun pi, composePerm
       (findPermEq (-(s{2}.`2.`1 - s{2}.`1 *^ (w{1}.`2.`1 || w{1}.`1.`1))) U.bW{2})  pi{2})
     (fun pi, (composePerm (invPerm
           (findPermEq (-(s{2}.`2.`1 - s{2}.`1 *^ (w{1}.`2.`1 || w{1}.`1.`1))) U.bW{2}))  pi{2})).

     (* Sample b0 *) rnd{2}.
     (* Create sub goals*) auto. progress.
     (* Show smapling works b0 and pi *) apply chi_ll. rewrite -composePermA. apply findPermChecks.
     apply invPermPerm. apply findPermChecks. smt(@Perms @List @Distr). rewrite composePermNeg. apply findPermChecks.
             rewrite composePermID. trivial. smt(@Perms @List @Distr). trivial. apply mu1Perm. smt(@Perms @List @Distr).
             apply composePermPerm. apply invPermPerm. apply findPermChecks. smt(@Perms @List @Distr). apply isPermSimp2.
             apply composePermPerm. apply findPermChecks. smt(@Perms @List @Distr).
    rewrite -composePermA. apply invPermPerm. apply findPermChecks.
     apply findPermChecks. smt(@Perms @List @Distr). rewrite composePermNeg. apply findPermChecks.
             rewrite composePermID. smt(@Perms @List @Distr). trivial.
    rewrite -composePermA. apply findPermChecks.
     apply invPermPerm. apply findPermChecks. smt(@Perms @List @Distr). rewrite composePermNeg. apply findPermChecks.
             rewrite composePermID. trivial. smt(@Perms @List @Distr). trivial. apply mu1Perm. smt(@Perms @List @Distr).
             apply composePermPerm. apply invPermPerm. apply findPermChecks. smt(@Perms @List @Distr). apply isPermSimp2.
             apply composePermPerm. apply findPermChecks. smt(@Perms @List @Distr).
    rewrite -composePermA. apply invPermPerm. apply findPermChecks.
     apply findPermChecks. smt(@Perms @List @Distr). rewrite composePermNeg. apply findPermChecks.
             rewrite composePermID. smt(@Perms @List @Distr). trivial.
    rewrite -composePermA. apply findPermChecks.
     apply invPermPerm. apply findPermChecks. smt(@Perms @List @Distr). rewrite composePermNeg. apply findPermChecks.
             rewrite composePermID. trivial. smt(@Perms @List @Distr). trivial. apply mu1Perm. smt(@Perms @List @Distr).
             apply composePermPerm. apply invPermPerm. apply findPermChecks. smt(@Perms @List @Distr). apply isPermSimp2.
             apply composePermPerm. apply findPermChecks. smt(@Perms @List @Distr).
    rewrite -composePermA. apply invPermPerm. apply findPermChecks.
     apply findPermChecks. smt(@Perms @List @Distr). rewrite composePermNeg. apply findPermChecks.
             rewrite composePermID. smt(@Perms @List @Distr). trivial.
    (* samling f *) rewrite composePermCorrect. smt(@M). apply findPermChecks. apply invPermPerm. apply findPermChecks.
    rewrite composePermNeg. apply findPermChecks. rewrite permVectorID; trivial. smt(@M). apply dRpermPres. apply findPermChecks.
    smt(@MLWE.M). apply dRpermPres2. smt(@M). apply invPermPerm. apply findPermChecks. rewrite composePermCorrect.
    smt(@M). apply invPermPerm. apply findPermChecks. apply findPermChecks. rewrite composePermNeg. apply findPermChecks.
    rewrite permVectorID. smt(@MLWE.M). trivial.
    rewrite composePermCorrect. smt(@M). apply findPermChecks. apply invPermPerm. apply findPermChecks.
    rewrite composePermNeg. apply findPermChecks. rewrite permVectorID; trivial. smt(@M). apply dRpermPres. apply findPermChecks.
    smt(@MLWE.M). apply dRpermPres2. smt(@M). apply invPermPerm. apply findPermChecks. rewrite composePermCorrect.
    smt(@M). apply invPermPerm. apply findPermChecks. apply findPermChecks. rewrite composePermNeg. apply findPermChecks.
             rewrite permVectorID. smt(@MLWE.M). trivial.
    rewrite composePermCorrect. smt(@M). apply findPermChecks. apply invPermPerm. apply findPermChecks.
    rewrite composePermNeg. apply findPermChecks. rewrite permVectorID; trivial. smt(@M). apply dRpermPres. apply findPermChecks.
    smt(@MLWE.M). apply dRpermPres2. smt(@M). apply invPermPerm. apply findPermChecks. rewrite composePermCorrect.
    smt(@M). apply invPermPerm. apply findPermChecks. apply findPermChecks. rewrite composePermNeg. apply findPermChecks.
    rewrite permVectorID. smt(@MLWE.M). trivial.

     apply commit_rand_ll.
     (* c message *)
     rewrite !bRing. apply commit_message_eq. rewrite -!composePermA. apply invPermPerm. apply findPermChecks. apply findPermChecks.
     apply isPermSimp; trivial. apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial.
     apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. rewrite !composePermNeg.
      apply findPermChecks. apply findPermChecks.  apply findPermChecks. rewrite !composePermID.
      apply isPermSimp; trivial. apply isPermSimp; trivial. apply isPermSimp; trivial. trivial.
     (* c1 message *)
     rewrite !bRing. rewrite !composePermCorrect. smt(@MLWE.M). apply invPermPerm. apply findPermChecks. apply findPermChecks.
     smt(@MLWE.M). apply invPermPerm. apply findPermChecks. apply findPermChecks. smt(@MLWE.M). apply invPermPerm.
     apply findPermChecks. apply findPermChecks. rewrite !composePermNeg. apply findPermChecks. apply findPermChecks.
     apply findPermChecks. rewrite !permVectorID. smt(@MLWE.M).  smt(@MLWE.M).  smt(@MLWE.M). trivial.
     (* c2 message *)
     rewrite !bRing. rewrite !composePermCorrect. smt(@M). apply invPermPerm. apply findPermChecks. apply composePermPerm.
     apply findPermChecks. apply isPermSimp; trivial. smt(@M). apply invPermPerm. apply findPermChecks. apply composePermPerm.
     apply findPermChecks. apply isPermSimp; trivial. smt(@M). apply invPermPerm. apply findPermChecks. apply composePermPerm.
     apply findPermChecks. apply isPermSimp; trivial. rewrite -!composePermA. apply invPermPerm. apply findPermChecks.
     apply findPermChecks. apply isPermSimp; trivial.  apply invPermPerm. apply findPermChecks.
     apply findPermChecks. apply isPermSimp; trivial. apply invPermPerm. apply findPermChecks.
     apply findPermChecks. apply isPermSimp; trivial. rewrite !composePermNeg; try apply findPermChecks.
     rewrite !composePermID; try apply isPermSimp; trivial.  
     (* c4 message *)
     rewrite !bRing. apply commit_message_eq. split. apply (t3_e2); trivial. apply isPermSimp; trivial. smt(@M). smt(). smt().
     apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. rewrite eq_sym.
             rewrite chi_weight. smt(). elim Rel => Rel0 Rel. rewrite bRing in Rel0. smt().  smt(chi_k).
      apply (t3_e2); trivial. apply isPermSimp; trivial. smt(@M). smt(). smt().
     apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. rewrite eq_sym.
             rewrite chi_weight. smt(). elim Rel => Rel0 [Rel1 Rel]. rewrite bRing in Rel1. smt().  smt(chi_k).
      apply (t3_e2); trivial. apply isPermSimp; trivial. smt(@M). smt(). smt().
     apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. rewrite eq_sym.
             rewrite chi_weight. smt(). elim Rel => Rel0 [Rel1 [Rel2 Rel]]. rewrite bRing in Rel2. smt().  smt(chi_k).
     (* t1 *)
     rewrite !bRing. rewrite !composePermCorrect. smt(@MLWE.M). apply invPermPerm. apply findPermChecks.
     apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA. 
     apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. rewrite !composePermNeg.
             apply findPermChecks. rewrite composePermID. apply isPermSimp; trivial. trivial.
     rewrite !bRing. rewrite !composePermCorrect. smt(@MLWE.M). apply invPermPerm. apply findPermChecks.
     apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA. 
     apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. rewrite !composePermNeg.
             apply findPermChecks. rewrite composePermID. apply isPermSimp; trivial. trivial.
     rewrite !bRing. rewrite !composePermCorrect. smt(@MLWE.M). apply invPermPerm. apply findPermChecks.
     apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA. 
     apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. rewrite !composePermNeg.
     apply findPermChecks. rewrite composePermID. apply isPermSimp; trivial. trivial.
     (* t2 *)
     rewrite !bRing. apply t3_e2; trivial.  apply isPermSimp; trivial. smt(@M). smt(). smt().
     apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. rewrite eq_sym.
             rewrite chi_weight. smt(). elim Rel => Rel0 Rel. rewrite bRing in Rel0. smt().  smt(chi_k).
     rewrite !bRing. apply (t3_e2); trivial. apply isPermSimp; trivial. smt(@M). smt(). smt().
     apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. rewrite eq_sym.
             rewrite chi_weight. smt(). elim Rel => Rel0 [Rel1 Rel]. rewrite bRing in Rel1. smt().  smt(chi_k).
     rewrite !bRing. apply (t3_e2); trivial. apply isPermSimp; trivial. smt(@M). smt(). smt().
     apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. rewrite eq_sym.
             rewrite chi_weight. smt(). elim Rel => Rel0 [Rel1 [Rel2 Rel]]. rewrite bRing in Rel2. smt().  smt(chi_k).
     (* c2 opening *)
     rewrite !bRing. rewrite !composePermCorrect. smt(@M). apply invPermPerm. apply findPermChecks. apply composePermPerm.
     apply findPermChecks. apply isPermSimp; trivial. smt(@M). apply invPermPerm. apply findPermChecks. apply composePermPerm.
     apply findPermChecks. apply isPermSimp; trivial. smt(@M). apply invPermPerm. apply findPermChecks. apply composePermPerm.
     apply findPermChecks. apply isPermSimp; trivial. rewrite -!composePermA. apply invPermPerm. apply findPermChecks.
     apply findPermChecks. apply isPermSimp; trivial.  apply invPermPerm. apply findPermChecks.
     apply findPermChecks. apply isPermSimp; trivial. apply invPermPerm. apply findPermChecks.
     apply findPermChecks. apply isPermSimp; trivial. rewrite !composePermNeg; try apply findPermChecks.
     rewrite !composePermID; try apply isPermSimp; trivial.  
             (* c2 opening *)
     rewrite !bRing. rewrite !composePermCorrect. smt(@M). apply invPermPerm. apply findPermChecks. apply composePermPerm.
     apply findPermChecks. apply isPermSimp; trivial. smt(@M). apply invPermPerm. apply findPermChecks. apply composePermPerm.
     apply findPermChecks. apply isPermSimp; trivial. smt(@M). apply invPermPerm. apply findPermChecks. apply composePermPerm.
     apply findPermChecks. apply isPermSimp; trivial. rewrite -!composePermA. apply invPermPerm. apply findPermChecks.
     apply findPermChecks. apply isPermSimp; trivial.  apply invPermPerm. apply findPermChecks.
     apply findPermChecks. apply isPermSimp; trivial. apply invPermPerm. apply findPermChecks.
     apply findPermChecks. apply isPermSimp; trivial. rewrite !composePermNeg; try apply findPermChecks.
     rewrite !composePermID; try apply isPermSimp; trivial.  
             (* c3 opening *)
     rewrite !bRing. apply commit_open_eq. split. apply t3_e2; trivial.  apply isPermSimp; trivial. smt(@M). smt(). smt().
     apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. rewrite eq_sym.
             rewrite chi_weight. smt(). elim Rel => Rel0 Rel. rewrite bRing in Rel0. smt().  smt(chi_k).
      apply (t3_e2); trivial. apply isPermSimp; trivial. smt(@M). smt(). smt().
     apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. rewrite eq_sym.
             rewrite chi_weight. smt(). elim Rel => Rel0 [Rel1 Rel]. rewrite bRing in Rel1. smt().  smt(chi_k).
      apply (t3_e2); trivial. apply isPermSimp; trivial. smt(@M). smt(). smt().
     apply permEqWeight. smt(). smt(@MLWE.M). apply chi_k. trivial. rewrite eq_sym.
             rewrite chi_weight. smt(). elim Rel => Rel0 [Rel1 [Rel2 Rel]]. rewrite bRing in Rel2. smt().  smt(chi_k).
    qed.
   
     lemma ValidOpen_ZK s w e &m :
       R s w =>
       e \in range 0 3 =>
       islossless D.distinguish =>
       Pr[SHVZK(LinearRelProt, LinearRelAlg, D).simulate(s,e) @ &m : res] -
       Pr[SHVZK(LinearRelProt, LinearRelAlg, D).real(s,w,e) @ &m : res] <=
       Pr[HidingExperimentL(U(D)).main((s,w,e)) @ &m : res] - Pr[HidingExperimentR(U(D)).main((s,w,e)) @ &m : res].
   proof.
     move => @/R Rel Ran ll. rewrite (Real_GB_0 s w e &m); trivial. rewrite(Real_GB_1 s w e &m); trivial.
   qed.

 
     
   
     
     
