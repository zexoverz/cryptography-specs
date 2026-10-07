import EthCryptographySpecs.Xmss.Serialization
import EthCryptographySpecs.Proofs.Xmss.Verify

/-!
# Proofs: `Xmss.Serialization`

The wire layout, pinned on the reference key and signature of
`Proofs/Xmss/Verify.lean`.

What the cases below are for is the field order. A round trip alone says
nothing about it: encoder and decoder agree under any ordering they share,
so the position of each field is checked against the byte offsets the
specification names, not against the decoder.

The general round-trip and surjectivity statements are not here. They need
lemmas about reading one field out of a concatenation that do not exist yet.

The 32-byte public key cases stay kernel-checked. The signature cases run on
`native_decide`: 1208 bytes of array literal is past what the kernel's
evaluator finishes in reasonable time.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Lengths

Exact, and the only validation either decoder performs. -/

/-- The reference public key encodes to the advertised 32 bytes. -/
theorem size_toBytes_examplePublicKey :
    examplePublicKey.toBytes.size = PUB_KEY_SIZE := by
  decide +kernel

/-- The reference signature encodes to the advertised 1208 bytes. -/
theorem size_toBytes_exampleSignature :
    exampleSignature.toBytes.size = SIG_SIZE := by
  native_decide

/-- A byte too many is rejected, not truncated. -/
theorem fromBytes_exampleSignature_too_long :
    (Signature.fromBytes (exampleSignature.toBytes.push 0)).toOption = none := by
  native_decide

/-- A byte too few is rejected, not padded. -/
theorem fromBytes_exampleSignature_too_short :
    (Signature.fromBytes
      (exampleSignature.toBytes.extract 0 (SIG_SIZE - 1))).toOption = none := by
  native_decide

/-! ## Round trip -/

/-- Decoding the reference public key's encoding returns that key. -/
theorem fromBytes_toBytes_examplePublicKey :
    (PublicKey.fromBytes examplePublicKey.toBytes).toOption
      = some examplePublicKey := by
  decide +kernel

/-- Decoding the reference signature's encoding returns that signature. -/
theorem fromBytes_toBytes_exampleSignature :
    (Signature.fromBytes exampleSignature.toBytes).toOption
      = some exampleSignature := by
  native_decide

/-! ## Wire order

Each field is read at the offset the layout gives it. Encoding and decoding
are not compared against each other here: both are compared against the
offsets. -/

/-- The public key opens with the Merkle root. -/
theorem toBytes_examplePublicKey_root_first :
    (examplePublicKey.toBytes.extract 0 DIGEST_LEN).data
      = (packBytes examplePublicKey.merkleRoot).data := by
  decide +kernel

/-- The public parameter follows the root. -/
theorem toBytes_examplePublicKey_publicParam_second :
    (examplePublicKey.toBytes.extract DIGEST_LEN PUB_KEY_SIZE).data
      = (packBytes examplePublicKey.publicParam).data := by
  decide +kernel

/-- The signature opens with the first chain value. -/
theorem toBytes_exampleSignature_chain_first :
    (exampleSignature.toBytes.extract 0 DIGEST_LEN).data
      = (packBytes exampleSignature.chainElements[0]).data := by
  native_decide

/-- The randomizer sits after all 42 chain values, at offset 672.

This is the ordering the issue exists to fix: the note writes a signature as
`(rho, chain values, path)`, and that is not the wire order. -/
theorem toBytes_exampleSignature_randomness_after_chains :
    (exampleSignature.toBytes.extract (V * DIGEST_LEN) WOTS_SIG_SIZE).data
      = (packBytes exampleSignature.randomness).data := by
  native_decide

/-- The randomizer is *not* at the front.

Without this the suite passes under a rho-first encoder, because every other
case above holds of one. -/
theorem toBytes_exampleSignature_randomness_not_first :
    (exampleSignature.toBytes.extract 0 RANDOMNESS_LEN).data
      ≠ (packBytes exampleSignature.randomness).data := by
  native_decide

/-- The authentication path follows the randomizer, at offset 696. -/
theorem toBytes_exampleSignature_path_after_randomness :
    (exampleSignature.toBytes.extract WOTS_SIG_SIZE
      (WOTS_SIG_SIZE + DIGEST_LEN)).data
      = (packBytes exampleSignature.merklePath[0]).data := by
  native_decide

/-- The last sibling ends the signature. -/
theorem toBytes_exampleSignature_path_last :
    (exampleSignature.toBytes.extract (SIG_SIZE - DIGEST_LEN) SIG_SIZE).data
      = (packBytes exampleSignature.merklePath[LOG_LIFETIME - 1]).data := by
  native_decide

/-! ## Wire order, from the decoder's side

The cases above pin the encoder. These feed in a buffer nobody encoded, byte
`i` holding `i`, so each field's contents name the offset it was read from. -/

/-- A signature-length buffer whose byte `i` is `i` modulo 256. -/
def countingSignatureBytes : ByteArray :=
  ⟨Array.ofFn (n := SIG_SIZE) fun i => UInt8.ofNat i.val⟩

/-- The first chain value is read from offset 0. -/
theorem fromBytes_countingSignatureBytes_chain_first :
    ((Signature.fromBytes countingSignatureBytes).toOption.map
      fun sig => sig.chainElements[0].toArray)
      = some (Array.ofFn (n := DIGEST_LEN) fun i => UInt8.ofNat i.val) := by
  native_decide

/-- The randomizer is read from offset 672, after the chain values. -/
theorem fromBytes_countingSignatureBytes_randomness :
    ((Signature.fromBytes countingSignatureBytes).toOption.map
      fun sig => sig.randomness.toArray)
      = some (Array.ofFn (n := RANDOMNESS_LEN) fun i =>
          UInt8.ofNat (V * DIGEST_LEN + i.val)) := by
  native_decide

/-- The first sibling is read from offset 696, after the randomizer. -/
theorem fromBytes_countingSignatureBytes_path_first :
    ((Signature.fromBytes countingSignatureBytes).toOption.map
      fun sig => sig.merklePath[0].toArray)
      = some (Array.ofFn (n := DIGEST_LEN) fun i =>
          UInt8.ofNat (WOTS_SIG_SIZE + i.val)) := by
  native_decide

end EthCryptographySpecs.Xmss
