# tls.bend: TLS 1.3 wire encoding for the client side (RFC 8446): the record
# layer with TLS_CHACHA20_POLY1305_SHA256, and the handshake messages a client
# sends (ClientHello) or reads. Bytes are List<&2, U32> (0..255).

import Base
import ./chacha20.bend as C
import ./aead.bend as A

# Numbers and bytes
# -----------------

# the k-byte big-endian encoding of n, in front of acc
def tls.be.acc(k: Nat, +n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      tls.be.acc(p, Nat.div(n, 256n), U32.from_nat(Nat.mod(n, 256n)) <> acc)

def tls.be(k: Nat, +n: Nat) -> List<&2, U32>:
  tls.be.acc(k, n, Nil{})

def tls.cat(+xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

def tls.zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      (0 : U32) <> tls.zeros(p)

def tls.len(+xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      tls.len(t, 1n+acc)

# a vector with a k-byte length prefix
def tls.vec(k: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  tls.cat(tls.be(k, tls.len(xs, 0n)), xs)

# a handshake message: type, 3-byte length, body
def tls.hs(t: U32, +body: List<&2, U32>) -> List<&2, U32>:
  t <> tls.cat(tls.be(3n, tls.len(body, 0n)), body)

# Record layer
# ------------

# the per-record nonce: the IV xor the 8-byte big-endian sequence number
def tls.nonce(+iv: List<&2, U32>, seq: Nat) -> List<&2, U32>:
  C.cc.xorb(iv, tls.cat(tls.zeros(4n), tls.be(8n, seq)))

# the 5-byte header of an encrypted record whose content is n bytes long
def tls.header(n: Nat) -> List<&2, U32>:
  23 <> 3 <> 3 <> tls.be(2n, n)

# a protected record: header, then the AEAD of the content and its type byte
def tls.seal.at(+key: List<&2, U32>, +iv: List<&2, U32>, seq: Nat, +pt: List<&2, U32>,
  +hdr: List<&2, U32>, ctype: U32) -> List<&2, U32>:
  tls.cat(hdr, A.aead_seal_any(key, tls.nonce(iv, seq), hdr, tls.cat(pt, ctype <> Nil{})))

# a plaintext record (no protection): type, legacy version 0x0301, length, body
def tls.seal(+key: List<&2, U32>, +iv: List<&2, U32>, seq: Nat, ctype: U32, +pt: List<&2, U32>) ->
  List<&2, U32>:
  tls.seal.at(key, iv, seq, pt, tls.header(tls.len(pt, 17n)), ctype)

def tls.plain(ctype: U32, +body: List<&2, U32>) -> List<&2, U32>:
  ctype <> 3 <> 1 <> tls.cat(tls.be(2n, tls.len(body, 0n)), body)

# ClientHello (RFC 8446 section 4.1.2) with TLS_CHACHA20_POLY1305_SHA256, x25519
# key share, supported_versions, supported_groups, signature_algorithms
# (rsa_pss_rsae_sha256 and rsa_pkcs1_sha256) and the server name
def tls.key_share(+pub: List<&2, U32>, +pubp: List<&2, U32>) -> List<&2, U32>:
  tls.cat(0 <> 51 <> Nil{}, tls.vec(2n, tls.vec(2n, tls.cat(0 <> 29 <> Nil{}, tls.cat(tls.vec(2n, pub),
    tls.cat(0 <> 23 <> Nil{}, tls.vec(2n, pubp)))))))

def tls.server_name(+host: List<&2, U32>) -> List<&2, U32>:
  tls.cat(0 <> 0 <> Nil{}, tls.vec(2n, tls.vec(2n, 0 <> tls.vec(2n, host))))

def tls.exts(+pub: List<&2, U32>, +pubp: List<&2, U32>, +host: List<&2, U32>) -> List<&2, U32>:
  tls.cat(0 <> 43 <> 0 <> 3 <> 2 <> 3 <> 4 <> Nil{}, tls.cat(0 <> 10 <> 0 <> 6 <> 0 <> 4 <> 0 <> 29 <> 0 <> 23 <> Nil{},
    tls.cat(0 <> 13 <> 0 <> 10 <> 0 <> 8 <> 8 <> 4 <> 4 <> 1 <> 4 <> 3 <> 8 <> 7 <> Nil{},
    tls.cat(tls.key_share(pub, pubp), tls.server_name(host)))))

def tls.client_hello(+random: List<&2, U32>, +pub: List<&2, U32>, +pubp: List<&2, U32>, +host: List<&2, U32>) -> List<&2, U32>:
  tls.hs(1, tls.cat(3 <> 3 <> Nil{}, tls.cat(random, tls.cat(0 <> Nil{},
    tls.cat(tls.vec(2n, 19 <> 1 <> 19 <> 3 <> Nil{}), tls.cat(1 <> 0 <> Nil{},
    tls.vec(2n, tls.exts(pub, pubp, host))))))))

# Reading the server's messages
# -----------------------------

# the big-endian number of the first k bytes of bs
def tls.num(k: Nat, +bs: List<&2, U32>) -> Nat:
  match k:
    case 0n:
      0n
    case 1n++p:
      match bs:
        case Nil{}:
          0n
        case b <> t:
          Nat.add(Nat.mul(U32.to_nat(b), Nat.pow(256n, p)), tls.num(p, t))

# the handshake message at the front of bs: its type, its body, and the rest
type HM is Data:
  HM{t: U32, body: List<&2, U32>, rest: List<&2, U32>}

def tls.hm.at(t: U32, +n: Nat, +r: List<&2, U32>) -> HM:
  HM{t, List.take(&2, U32, List.drop(&2, U32, r, 3n), n), List.drop(&2, U32, r, Nat.add(3n, n))}

# the extension list of a handshake body's extensions field (2-byte length first)
def tls.hm(+bs: List<&2, U32>) -> HM:
  match bs:
    case Nil{}:
      HM{0, Nil{}, Nil{}}
    case t <> r:
      tls.hm.at(t, tls.num(3n, r), r)

def tls.vec16(+xs: List<&2, U32>) -> List<&2, U32>:
  List.take(&2, U32, List.drop(&2, U32, xs, 2n), tls.num(2n, xs))

# the extension with type t in the list xs (type, length, data), or Nil; hit
# says whether the first entry is the one wanted
def tls.ext.find(fuel: Nat, +xs: List<&2, U32>, +t: Nat, hit: Bool) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      match hit:
        case True{}:
          List.take(&2, U32, List.drop(&2, U32, xs, 4n), tls.num(2n, List.drop(&2, U32, xs, 2n)))
        case False{}:
          tls.ext.find(p, List.drop(&2, U32, xs, Nat.add(4n, tls.num(2n, List.drop(&2, U32, xs, 2n)))), t,
            Nat.is_eq(tls.num(2n, List.drop(&2, U32, xs, Nat.add(4n, tls.num(2n, List.drop(&2, U32, xs, 2n))))), t))

# the content of extension t in the extension list xs
def tls.ext(+xs: List<&2, U32>, +t: Nat) -> List<&2, U32>:
  tls.ext.find(1000000n, xs, t, Nat.is_eq(tls.num(2n, xs), t))

# ServerHello (RFC 8446 section 4.1.3): the position of the cipher suite
# (after the legacy session id) and the extension list
def tls.sh.cipher_at(+body: List<&2, U32>) -> Nat:
  Nat.add(35n, tls.num(1n, List.drop(&2, U32, body, 34n)))

def tls.sh.cipher(+body: List<&2, U32>) -> Nat:
  tls.num(2n, List.drop(&2, U32, body, tls.sh.cipher_at(body)))

def tls.sh.exts(+body: List<&2, U32>) -> List<&2, U32>:
  tls.vec16(List.drop(&2, U32, body, Nat.add(tls.sh.cipher_at(body), 3n)))

# the x25519 key share of a ServerHello: group (2), length (2), the 32 bytes
def tls.sh.key(+body: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, tls.ext(tls.sh.exts(body), 51n), 4n)

# the group of the server's key share: 29 (x25519) or 23 (secp256r1)
def tls.sh.group(+body: List<&2, U32>) -> Nat:
  tls.num(2n, tls.ext(tls.sh.exts(body), 51n))

# Certificate (RFC 8446 section 4.4.2): the certificate_list entries (DER). Each
# entry is a 3-byte length and the certificate, then a 2-byte extensions block.
def tls.certs.step(+xs: List<&2, U32>) -> Nat:
  Nat.add(Nat.add(3n, tls.num(3n, xs)), Nat.add(2n, tls.num(2n, List.drop(&2, U32, xs, Nat.add(3n, tls.num(3n, xs))))))

# the DER certificates of a Certificate message body (the request context first)
def tls.certs.go(fuel: Nat, +xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case x <> t:
          List.take(&2, U32, List.drop(&2, U32, xs, 3n), tls.num(3n, xs))
            <> tls.certs.go(p, List.drop(&2, U32, xs, tls.certs.step(xs)))

# the size of the entry at the front of xs: its length prefix, certificate and
# extensions block
def tls.certs(+body: List<&2, U32>) -> List<&2, List<&2, U32>>:
  tls.certs.go(1000000n, List.drop(&2, U32, body, Nat.add(4n, tls.num(1n, body))))

# the first byte of a list (the type of a handshake message), or 0
def tls.tag(+xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case x <> t:
      x
