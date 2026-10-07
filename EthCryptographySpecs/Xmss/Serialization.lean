import EthCryptographySpecs.Xmss.Errors
import EthCryptographySpecs.Xmss.Verify

/-!
# `Xmss.Serialization`

The SSZ encoding of a public key and a signature.

Public keys and signatures appear in consensus data, so they carry the
encoding the rest of the consensus layer uses. Both are containers of
fixed-size byte vectors, and SSZ encodes such a container as the plain
concatenation of its fields: no offsets, no length prefixes.

```text
public key  root (16) ‖ P (16)                                 = 32 bytes
signature   42 chain values (16) ‖ rho (24) ‖ 32 siblings (16)  = 1208 bytes
```

The randomizer sits *after* the chain values, even though the note writes a
signature as the tuple `(rho, chain values, path)`. The struct order is not
the wire order.

There is no canonical-form condition to enforce, unlike a compressed BLS
point: every byte string of the right length decodes to exactly one object.
So the length is the only validation, and it is exact. A buffer that is
shorter or longer is rejected, never padded and never truncated.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Public key -/

/-- The SSZ encoding of a public key: the root, then the public parameter. -/
def PublicKey.toBytes (pk : PublicKey) : ByteArray :=
  packBytes pk.merkleRoot ++ packBytes pk.publicParam

/-- Read a public key out of exactly `PUB_KEY_SIZE` bytes.

Fails with `badPublicKeySize` on any other length. -/
def PublicKey.fromBytes (b : ByteArray) : Except XmssError PublicKey :=
  -- The length check is the whole validation, and it is exact.
  if b.size ≠ PUB_KEY_SIZE then
    .error (.badPublicKeySize b.size)
  else
    match unpackBytes? DIGEST_LEN b 0,
          unpackBytes? PUBLIC_PARAM_LEN b DIGEST_LEN with
    | some merkleRoot, some publicParam => .ok { merkleRoot, publicParam }
    -- Unreachable: a buffer of exactly `PUB_KEY_SIZE` has room for both.
    | _, _ => .error (.badPublicKeySize b.size)

/-! ## Digest sequences

The chain values and the authentication path are both runs of digests, laid
down back to back. -/

/-- Concatenate a run of digests, in order. -/
def packDigests {k : Nat} (ds : Vector Digest k) : ByteArray :=
  ds.foldl (fun acc d => acc ++ packBytes d) ByteArray.empty

/-- Read `k` consecutive digests out of `b`, starting at `offset`.

Returns nothing when the buffer has no room for all of them. -/
def unpackDigests? (k : Nat) (b : ByteArray) (offset : Nat) :
    Option (Vector Digest k) :=
  -- Digest `i` occupies `[offset + i * 16, offset + (i + 1) * 16)`.
  (Vector.range k).mapM fun i => unpackBytes? DIGEST_LEN b (offset + i * DIGEST_LEN)

/-! ## Signature -/

/-- The SSZ encoding of a signature.

The 42 chain values, then the randomizer, then the 32 siblings. -/
def Signature.toBytes (sig : Signature) : ByteArray :=
  packDigests sig.chainElements
    ++ packBytes sig.randomness
    ++ packDigests sig.merklePath

/-- Read a signature out of exactly `SIG_SIZE` bytes.

Fails with `badSignatureSize` on any other length. -/
def Signature.fromBytes (b : ByteArray) : Except XmssError Signature :=
  if b.size ≠ SIG_SIZE then
    .error (.badSignatureSize b.size)
  else
    -- The randomizer starts where the chain values end, and the path starts
    -- where the randomizer ends.
    match unpackDigests? V b 0,
          unpackBytes? RANDOMNESS_LEN b (V * DIGEST_LEN),
          unpackDigests? LOG_LIFETIME b WOTS_SIG_SIZE with
    | some chainElements, some randomness, some merklePath =>
        .ok { chainElements, randomness, merklePath }
    -- Unreachable: a buffer of exactly `SIG_SIZE` has room for all three.
    | _, _, _ => .error (.badSignatureSize b.size)

end EthCryptographySpecs.Xmss
