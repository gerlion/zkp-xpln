This folder contains the EasyCrypt (https://github.com/EasyCrypt/easycrypt) proofs of the commitment scheme and zero-knowledge proofs from "Commitments and Efficient Zero-Knowledge
Proofs from Learning Parity with Noise"
Abhishek Jain, Stephan Krenn, Krzysztof Pietrzak, Aris Tentes (https://eprint.iacr.org/2012/513.pdf)

Specifically we proved concrete (as distinct from asymptotic) versions of:
    Theorem 3.1, Theorem 4.1, Theorem 4.2, and Theorem 4.3.
    
The following are files and their contents:
  SigmaProtocol3.ec    - a variant of the standard EasyCrypt SigmaProtocol encoding with the alteration that the special-soundness extractor gets three accepting transcripts not two.
  MLWE.ec              - An encoding of the decisional MLWE problem based on the existing dynamic matrix EasyCrypt library.
  Commitment_aux.ec    - A variation of the standard EasyCrypt commitment library which gives the adversary additional global information and gives the adversary access to pairs of messages
  
  JKPT12_aux.ec        - Formalises various dependencies including permutations, images, and sampling with certain norms.
  JKPT12_com.ec        - Formalises the JKPT12 commitment scheme and Theorem 3.1
  JKPT12_valid_open.ec - Formalises the ZKP of valid opening and Theorem 4.1
  JKPT12_lin_rel.ec    - Formalises the ZKP of linear relations and Theorem 4.2
  JKPT12_mul_rel.ec    - Formalises the ZKP of multiplicative relations and Theorem 4.3

This is version 1.1 of this project which includes the following improvements:
- Added more comments and removed some unnecessary axioms in JKPT12_aux.ec
- Made the commitment scheme in JKPT12_aux.ec explicitly randomised and imperfectly hiding
- Updated the various ZKPs with the updated commitment scheme

     
These proofs were developed and tested with the following configuration:
EasyCrypt commit - 9eaff01c7..22fe124e9
known provers: Alt-Ergo@2.4.2, Alt-Ergo[FPA]@2.4.2, CVC4@1.8.0, CVC4[counterexamples]@1.8.0, CVC4[strings]@1.8.0, CVC4[strings+counterexamples]@1.8.0, CVC5@1.0.5, CVC5[counterexamples]@1.0.5, CVC5[strings]@1.0.5, CVC5[strings+counterexamples]@1.0.5, Z3@4.12.6, Z3[counterexamples]@4.12.6, Z3[noBV]@4.12.6

To verify the EasyCrypt files run:

easycrypt SigmaProtocol3.ec; easycrypt MLWE.ec; easycrypt Commitment_aux.ec; easycrypt JKPT12_aux.ec; easycrypt JKPT12_com.ec; easycrypt JKPT12_valid_open.ec; easycrypt JKPT12_lin_rel.ec; easycrypt JKPT12_mul_rel.ec
