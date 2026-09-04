import Proof

open Kriterion Kriterion.BN254

theorem argoMACRandomizedEncodingCorrect [FieldCertificate] [GroupCertificate] :
    RandomizedEncoding.Correctness ArgoMAC.construction.randomizedEncoding :=
  ArgoMAC.construction.randomizedEncodingCorrect

theorem argoMACRandomizedEncodingPrivate [FieldCertificate] [GroupCertificate] :
    RandomizedEncoding.Privacy ArgoMAC.construction.randomizedEncoding
      ArgoMAC.construction.randomizedEncodingSimulator
      (RandomizedEncoding.uniformDistribution ArgoMAC.OffsetRandomness (List Point)) :=
  ArgoMAC.construction.randomizedEncodingPrivate

theorem argoMACOutputCount [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField)
    (randomness : ArgoMAC.OffsetRandomness) (point : Point) :
    (ArgoMAC.construction.outputs scalar randomness point).length = 91 :=
  ArgoMAC.construction.outputCount scalar randomness point

theorem argoMACPerfectCorrectness [FieldCertificate] [GroupCertificate]
    [ArgoMAC.TerminationCertificate] :
    GarbledCircuit.PerfectCorrectness
      (ArgoMAC.Garbling.garbledCircuit ArgoMAC.construction)
      (fun randomness =>
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)) :=
  ArgoMAC.RCBComplete.perfectCorrectness

def argoMACLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility
      (ArgoMAC.Garbling.garbledCircuit ArgoMAC.construction) affineLamportBits :=
  ArgoMAC.Lamport.compatible

#print axioms argoMACRandomizedEncodingCorrect
#print axioms argoMACRandomizedEncodingPrivate
#print axioms argoMACOutputCount
#print axioms argoMACPerfectCorrectness
#print axioms argoMACLamportCompatible
