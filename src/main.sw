contract;

mod lib;
use lib::{G1Point, G2Point, Scalar};
use std::hash::Hash;
use std::hash::{keccak256, sha256};
use std::bytes::Bytes;
use std::bytes_conversions::u256::*;


struct VerificationKey {
    // Scalars
    pub w1: Scalar,      // Root of unity
    pub q: Scalar,       // Scalar field size
    pub qf: Scalar,      // Base field size

    // G1 Points
    pub G1: G1Point,     // Generator of G1 ([1]_1)
    
    // G2 Points
    pub G2: G2Point,     // Generator of G2 ([1]_2)

    // Selector polynomials (G1 points)
    pub Qm: G1Point,     // Q_m(X)
    pub Ql: G1Point,     // Q_l(X)
    pub Qr: G1Point,     // Q_r(X)
    pub Qo: G1Point,     // Q_o(X)
    pub Qc: G1Point,     // Q_c(X)

    // Permutation polynomials (G1 points)
    pub S1: G1Point,     // S_1(X)
    pub S2: G1Point,     // S_2(X)
    pub S3: G1Point,     // S_3(X)

    // Scalars for permutation
    pub k1: Scalar,      // k1 (permutation factor)
    pub k2: Scalar,      // k2 (permutation factor)

    // Circuit metadata
    pub n: u32,          // Circuit size, power of 2
    pub nPublic: u16,    // Number of public inputs
    pub nLagrange: u16,  // Number of Lagrange polynomials

    // Additional points
    pub X2: G2Point,     // X2 point for additional checks
}


struct Proof {
  pub proof_A: G1Point,
  pub proof_B: G1Point,
  pub proof_C: G1Point,
  pub proof_Z: G1Point,
  pub proof_T1: G1Point,
  pub proof_T2: G1Point,
  pub proof_T3: G1Point,
  pub proof_Wxi: G1Point,
  pub proof_Wxiw: G1Point,
  pub eval_a: Scalar,
  pub eval_b: Scalar,
  pub eval_c: Scalar,
  pub eval_s1: Scalar,
  pub eval_s2: Scalar,
  pub eval_zw: Scalar,
}

fn reduce_mod(input: b256, q: u256) -> b256 {
    let mut temp: u256 = u256::from(input);
    // TODO is there a mod function?
    while temp >= q {
      temp -= q; 
    }
    let output: b256 = b256::from(temp);
    output
}

impl Proof {

    // beta, gamma, alpha, xi (=zeta), v, u
    fn get_challenges(self, vk: VerificationKey, publicInput: u256) -> [b256;6] {
        let mut transcript: Bytes = Bytes::new();

        ////// BETA
        // Qmx
        // Qmy
        transcript.append(vk.Qm.bytes());
        // Qlx
        // Qly
        transcript.append(vk.Ql.bytes());
        // Qrx
        // Qry
        transcript.append(vk.Qr.bytes());
        // Qox
        // Qoy
        transcript.append(vk.Qo.bytes());
        // Qcx
        // Qcy
        transcript.append(vk.Qc.bytes());
        // S1x
        // S1y
        transcript.append(vk.S1.bytes());
        // S2x
        // S2y
        transcript.append(vk.S2.bytes());
        // S3x
        // S3y
        transcript.append(vk.S3.bytes());
        // 32 bytes of public data
        transcript.append(Bytes::from(publicInput.to_be_bytes()));
        // 64 bytes of pA
        transcript.append(self.proof_A.bytes());
        // 64 bytes of pB
        transcript.append(self.proof_B.bytes());
        // 64 bytes of pC
        transcript.append(self.proof_C.bytes());
        // beta = hash(transcript) mod q
        let beta: b256 = reduce_mod(keccak256(transcript), vk.q.x);
        
        ////// GAMMA
        // gamma = hash(beta) mod q
        // Note: this follows snarkjs Plonk verifier beta = hash(transcript) and gamma = hash(beta)
        // While the paper does beta = hash(transcript, 0) and gamma=hash(transcript,1))
        let gamma: b256 = reduce_mod(keccak256(beta), vk.q.x);
        
        ////// ALPHA
        // alpha = hash(beta, gamma, proof_Z) mod q
        let mut transcript: Bytes = Bytes::new();
        transcript.append(Bytes::from(beta));
        transcript.append(Bytes::from(gamma));
        transcript.append(self.proof_Z.bytes());
        let alpha: b256 = reduce_mod(keccak256(transcript), vk.q.x);
        
        ////// XI (zeta in Plonk paper)
        // xi = hash(alpha, proof_T1, proof_T2, proof_T3) mod qs
        let mut transcript: Bytes = Bytes::new();
        transcript.append(Bytes::from(alpha));
        transcript.append(self.proof_T1.bytes());
        transcript.append(self.proof_T2.bytes());
        transcript.append(self.proof_T3.bytes());
        let xi: b256 = reduce_mod(keccak256(transcript), vk.q.x);

        ////// V
        // v = hash(xi, eval_a, eval_b, eval_c, eval_s1, eval_s2, eval_zw)
        let mut transcript: Bytes = Bytes::new();
        transcript.append(Bytes::from(xi));
        transcript.append(self.eval_a.bytes());
        transcript.append(self.eval_b.bytes());
        transcript.append(self.eval_c.bytes());
        transcript.append(self.eval_s1.bytes());
        transcript.append(self.eval_s2.bytes());
        transcript.append(self.eval_zw.bytes());
        let v: b256 = reduce_mod(keccak256(transcript), vk.q.x);

        ////// U
        // u = hash(wxi, wxiw)
        let mut transcript: Bytes = Bytes::new();
        transcript.append(self.proof_Wxi.bytes());
        transcript.append(self.proof_Wxiw.bytes());
        let u: b256 = reduce_mod(keccak256(transcript), vk.q.x);

        return [beta, gamma, alpha, xi, v, u]
    }

    // TODO calculate inverse to finish up the value
    fn calculateLagrange(self, vk: VerificationKey, zeta: u256, w: u256) -> (u256, u256) {
      // n(zeta-w) mod q
      let mut denom: u256 = 0;
      let temp = zeta - w;
      let n = u256::from(vk.n);
      // mem[$rA,32] = (b*c)%d
      asm (rA: denom, rB: temp, rC: n, rD: vk.q.x) {
        wqmm rA rB rC rD;
      };
      
      // 2. zeta^n-w, where in practice n is a power of 2
      let power = 11; // this is specific to the n (vk.n)
      let mut i = 0;
      let mut num: u256 = zeta;
      while i < power {
          // mem[$rA,32] = (b*c)%d
          asm (rA: num, rB: num, rC: num, rD: vk.q.x) {
            wqmm rA rB rC rD;
          };

          i = i + 1;
      }
      num = num - w;

      // TODO invert denom
      // return (zetaˆn-w) / n*(zeta-w)
      return (num, denom);
    }
      

    pub fn verify(self, vk: VerificationKey, publicInput: u256) -> bool {
        // 1. TODO check fields
        // 2. TODO check fields
        // 3. TODO check fields
        // Step 4: Recompute challenges beta, gamma, alpha, zeta, nu, and u in the field F
        // (β, γ, α, z, v, u)
        let challenges = self.get_challenges(vk, publicInput);
        let beta = u256::from(challenges[0]);
        let gamma = u256::from(challenges[1]);
        let alpha = u256::from(challenges[2]);
        let zeta = u256::from(challenges[3]);
        let nu = u256::from(challenges[4]);
        let u = u256::from(challenges[5]);

        // Step 5&6: compute w(z^n-1)/n*(z-w)
        let w: u256 = 1;
        let pEval_l1 = self.calculateLagrange(vk, zeta, w);

        return false;
    }
}

fn get_test_proof() -> Proof {
      let proof_A = G1Point{
      x: 0x03618765578723a3007c7307459f714a8ad0abf127d1d03f5941d0ef98fb3517u256,
      y: 0x166b1a9cd6b95072a5171d9b2c39fa40e09cf4c56f49ad64552ec343e71412c0u256
    };

    let proof_B = G1Point{
      x: 0x0c16e0ef7b10c89f84e065b34ff5e6727443c729687f887eb99224fcf9fdc199u256,
      y: 0x280e251de1f8fb27d7954f51226541b9275bc3e7f49887a33a4abb71867aac20u256
    };

    let proof_C = G1Point{
      x: 0x112178e206afd94afdc5382bbd29e11bf42acc58ba2abba243b07dbf78190fcdu256,
      y: 0x2620a43851c65e50b31095d8e665eda81071f57e876fc296616b87dfa005798du256
    };

    let proof_Z = G1Point{
      x: 0x08fc57ed374e950334f87bb22044a9e325bcae3240b2aece2324008d5b0d6e6du256,
      y: 0x2d8ff5876ac2271fca1c33369adf647c36a6b00542a0abfb83023cd620283020u256
    };

    let proof_T1 = G1Point{
      x: 0x18f85564bccfc77d56660bc9981f2c543e747b71b203a8d0a91dfcce50cf4adbu256,
      y: 0x0e8b209ae831b7144dd81c871e81f0ab278e1696f53841233d3ee51d09c6bcd9u256
    };

    let proof_T2 = G1Point{
      x: 0x17fd0eb60c51037364efcead597e1d9bd6460b2532aab73e280998a478d0d290u256,
      y: 0x27ccd04ff57cdd36bbd631af548c1834745303eef91ead7893d4acdbba4bcb80u256
    };

    let proof_T3 = G1Point{
      x: 0x06d02fe0c85bbc52b02177f7bdb2dc865b98704b354073219bd196b520a2cf18u256,
      y: 0x1ddf3e8658c7185f57b3f081672d5d2b6f5862c06e2b2ac13fa01f32d3af10bcu256
    };

    let proof_Wxi = G1Point{
      x: 0x13bbdbaabd814460f5521e6c3e79908c82ec82091c0110811c03347941ddb49cu256,
      y: 0x15ce85b2f0a8703eff8f870999e1ec1e8cbaec80863670da651c1f50541638b5u256
    };

    let proof_Wxiw = G1Point{
      x: 0x18c11243b75765c85d381199e961599a258e7c1153115bda9c057aeace228ec7u256,
      y: 0x18f0ab9da5c61b76ee039bee284da827a956b340956619771372f9a0418592dfu256
    };

    // eval_a
    let eval_a = Scalar {
        x: 0x1613045374eefb0a45f76b9f9ab656e96048ea161ae1b2dc9a5da5bc29bb652cu256,
    }; 
    // eval_b
    let eval_b = Scalar {
        x: 0x17041ee34f3535cd93a4ba84fb14ccf3efdf8c9bc7a6d1b9711ce8b49edddaddu256,
    };
    // eval_c
    let eval_c = Scalar {
        x: 0x2c4efe5b1ea056cd989493e5ddd05cf5320f77befd3d2499aeae5f86c42fae58u256,
    };
    // eval_s1
    let eval_s1 = Scalar {
        x: 0x1a53dd161c9ef92094825340d3bf5546e68c6456030d79c4cbcce67b1de4719du256,
    };
    // eval_s2
    let eval_s2 = Scalar {
        x: 0x12acc7b30823d540ce3a9e8531dcbee8dac99ce5b012e80f12e6624c9f0c5652u256,
    };
    // eval_zw
    let eval_zw = Scalar {
        x: 0x0f2ecb8cf64dbfa1d93c8fb63d93e2d4a33ebed3cdbef72c4d43d5eb87ff2bc5u256,
    };

    let proof = Proof {
      proof_A: proof_A,
      proof_B: proof_B,
      proof_C: proof_C,
      proof_Z: proof_Z,
      proof_T1: proof_T1,
      proof_T2: proof_T2,
      proof_T3: proof_T3,
      proof_Wxi: proof_Wxi,
      proof_Wxiw: proof_Wxiw,
      eval_a: eval_a,
      eval_b: eval_b,
      eval_c: eval_c,
      eval_s1: eval_s1,
      eval_s2: eval_s2,
      eval_zw: eval_zw,
    };

    return proof;
}

fn get_test_vk() -> VerificationKey {
  let vk = VerificationKey {
        w1: Scalar { x: 0x27a358499c5042bb4027fd7a5355d71b8c12c177494f0cad00a58f9769a2ee2u256 },
        q: Scalar { x: 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001u256 },
        qf: Scalar { x: 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47u256 },
        
        G1: G1Point { 
            x: 0x1u256, 
            y: 0x2u256 
        },
        
        G2: G2Point {
            x: [
                0x1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6edu256,
                0x198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2u256,
            ],
            y: [
                0x12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daau256,
                0x90689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975bu256,
            ]
        },
        
        Qm: G1Point { 
            x: 0x257a39d7a5bddadfbabe8ebd7df4c3521a1dbdd8cbbe6332cd609c8612a2ba29u256,
            y: 0xbaa231049c9662e040924014e3558475d2b6b4c5da421bfbb618dc863697bc8u256,
        },
        
        Ql: G1Point { 
            x: 0xa2b203e18cac0013e11d51531fdc50be9787f3ead6af16167163cf546d60aaeu256,
            y: 0x70fc6257f2227a99beffb1405d4bfd5bdec12539fde0a9ae66e3865a6e4785fu256,
        },
        
        Qr: G1Point { 
            x: 0xfe7a7ce1a2ccc939ed1f9c111eda6cbd56659574a632adddf01420a03ab3dbdu256,
            y: 0x199e3d497051629a5a9256871d04007760f7b9cfd071cd7c7ecae57eba577dc3u256,
        },
        
        Qo: G1Point { 
            x: 0x12e60366cf65d8075e8323b4901c327975ccd65c8099545b69bfc74d550f29c2u256,
            y: 0x1a88c9d927c1544a000aac6b4b790943b82eacec71818df67a5af62415d56b3cu256,
        },
        
        Qc: G1Point { 
            x: 0x0u256, 
            y: 0x0u256 
        },
        
        S1: G1Point { 
            x: 0x161290a46dfaa41fb95b6e638ebcbe4c70dad8aa3b037acf8e3dd0edf9007d9fu256,
            y: 0x135e57e5cddfacec05163e20b5e06dcae4c48d41ce60ebb9891eecc233bdaad5u256,
        },
        
        S2: G1Point { 
            x: 0xaac7d6f6a38ec02534a66751c1187ee71e008fbb785627c67495ed89408a20u256,
            y: 0x1f71f2bbc8116d6a4a01426bdfa8fa530567229617281c420be7450d10d9f715u256,
        },
        
        S3: G1Point { 
            x: 0x253b99253a85cc6aafeed98d2faac282b1ca968ebfad1e4e6bc6175fca522e94u256,
            y: 0x99316deda740d633d42b223d6a9a056ca722c8369f4d7a3ef35e051211fe40au256,
        },
        
        k1: Scalar { x: 0x2u256 },
        k2: Scalar { x: 0x3u256 },
        
        n: 2048,
        nPublic: 1,
        nLagrange: 1,

        X2: G2Point {
            x: [
                0xc1d680c2f37096c31e7291987346ef5924e35113defb301e6d16cc7838078e4u256,
                0xbad11ec876d25d407f42cfd057928f01cb833839dd05df6a6ec301d8506466du256,
            ],
            y: [
                0x880813632ca0535817a0b5a99e30072c16a287fe5b6949690c6792090e5d659u256,
                0x272b081cb84fe424a9c0baa28e9552abe502db30f3f3b57f7e51f21d1a0cf02eu256,
            ]
        },
    };
    
    return vk;
}

#[test]
fn test_challenges_correct() {
  let proof = get_test_proof();
  let vk = get_test_vk();
  let publicInput: u256 = 0x110d778eaf8b8ef7ac10f8ac239a14df0eb292a8d1b71340d527b26301a9ab08u256;
  let challenges = proof.get_challenges(vk, publicInput);
  // beta = 9039157458725624756817570435850936750907480212061850632293870469811624017805
  assert(challenges[0] == 0x13fbfb586deb4d87a24218bc40e77153fe065b3c8401a0ab729130bb9000ff8d);
  // gamma = 21183458777034922119798033548885077621097219042378882580873372273104224850007
  assert(challenges[1] == 0x2ed569abe2d859b264a1a976feb661c36cd14be653582a385d9d6f8c71451057);
  // alpha = 0x2a266571789ec0ac7ccf08b61ccac16c10e217f0c14b87eada1d6c9fe0e11dac
  assert(challenges[2] == 0x2a266571789ec0ac7ccf08b61ccac16c10e217f0c14b87eada1d6c9fe0e11dac);
  // xi = 5995391859610881302288530115281124419615446175822039475645465975985575599666
  // 0x0d4145839d4fdb8f5fd1533b384e24940bf7114b39cdd16f163838bbaeec9e32
  assert(challenges[3] == 0x0d4145839d4fdb8f5fd1533b384e24940bf7114b39cdd16f163838bbaeec9e32);
  // v = 10198407354444968769398716682395728712793326285861009311402838323692940309090
  // 0x168c1810dcfcb6d7bbee36e0140593e4382ca849c3d6539eaa1e2ebb84e83262
  assert(challenges[4] == 0x168c1810dcfcb6d7bbee36e0140593e4382ca849c3d6539eaa1e2ebb84e83262);
  // u = 14042079368063643215831999264291317274757448834632197026177557057575581413658
  // 0x1f0b89079ac8c5c8af6b1480eb3ad5661afb28ff7a4096f00422dc675d5c711a
  assert(challenges[5] == 0x1f0b89079ac8c5c8af6b1480eb3ad5661afb28ff7a4096f00422dc675d5c711a);
}

#[test]
fn test_calculate_lagrange() {
    let proof = get_test_proof();
    let vk = get_test_vk();
    let zeta: u256 = u256::from(0x0d4145839d4fdb8f5fd1533b384e24940bf7114b39cdd16f163838bbaeec9e32);
    let w: u256 = 1;
    
    // Returns num and denom separately, since inversion has not been implemented yet
    let (num, denom): (u256, u256) = proof.calculateLagrange(vk, zeta, w);
    // n(zeta-1) mod q: 0x2ec0819de24e1fbb5b015a8726335497c6fe3b4428e53aed437ca9da64f185d0
    assert(denom == u256::from(0x2ec0819de24e1fbb5b015a8726335497c6fe3b4428e53aed437ca9da64f185d0));
    // zeta^n - 1 mod q: 0x146415a35241c3305dc90bccb7aae026960aa78d380828893c63a7eb0ea81d97
    assert(num == u256::from(0x146415a35241c3305dc90bccb7aae026960aa78d380828893c63a7eb0ea81d97));

    // TODO add inversion and compute final value
    // let pEval_l1: u256 = proof.calculateLagrange(vk, zeta, w);
    // let expected_pEval_l1: u256 = u256::from(0x0e403813acb2c357cb815b0cf271a6f92851f0444081051ea884eb47fa36e9dd);
    // assert(pEval_l1 == expected_pEval_l1);
    
}

