package sign

/*
Extention for signing algorithms

Author: Roland Kromes
Contact: r.g.kromes@tudelft.nl
Institution: TU Delft - REIT Team

Author: Alin Roșu
Contact: A.Rou@student.tudelft.nl
Institution: TU Delft - Cyber Security Group

Description:
Extentions to allow deterministic usage of the elliptic curve digital signature algorithm following the RFC 6979 standard.
New extentions : Step1_with_rfc6979(...)
*/

import (
	"crypto/ecdsa"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"math/big"

	"github.com/decred/dcrd/dcrec/secp256k1/v2"
	"github.com/okx/threshold-lib/crypto"
	"github.com/okx/threshold-lib/crypto/commitment"
	"github.com/okx/threshold-lib/crypto/curves"
	"github.com/okx/threshold-lib/crypto/paillier"
	"github.com/okx/threshold-lib/crypto/schnorr"
)

type P2Context struct {
	sessionID *big.Int

	x2        *big.Int // x = x1 + x2
	E_x1      *big.Int
	paiPub    *paillier.PublicKey
	PublicKey *ecdsa.PublicKey
	message   string
	k2        *big.Int
	cmtC      *commitment.Commitment
}

// NewP1 2-party signature, P2 init
func NewP2(bobPri, E_x1 *big.Int, publicKey *ecdsa.PublicKey, paiPub *paillier.PublicKey, message string) *P2Context {
	msg, err := hex.DecodeString(message)
	if err != nil {
		return nil
	}
	data := new(big.Int).SetBytes(msg)
	sessionId := crypto.SHA256Int(publicKey.X, publicKey.Y, data)

	p2Context := &P2Context{
		x2:        bobPri,
		E_x1:      E_x1,
		paiPub:    paiPub,
		PublicKey: publicKey,
		message:   message,
		sessionID: sessionId,
	}
	return p2Context
}

func (p2 *P2Context) Step1(cmtC *commitment.Commitment) (*schnorr.Proof, *curves.ECPoint, error) {
	p2.cmtC = cmtC

	// random generate k2, k=k1*k2
	p2.k2 = crypto.RandomNum(curve.N)
	R2 := curves.ScalarToPoint(curve, p2.k2)
	proof, err := schnorr.ProveWithId(p2.sessionID, p2.k2, R2)
	if err != nil {
		return nil, nil, err
	}
	return proof, R2, nil
}

func (p2 *P2Context) Step1_with_rfc6979(x2 *big.Int, cmtC *commitment.Commitment) (*schnorr.Proof, *curves.ECPoint, error) {
	p2.cmtC = cmtC

	msg, _ := hex.DecodeString(p2.message)

	h := sha256.Sum256(msg)

	p2.k2 = secp256k1.NonceRFC6979(x2, h[:], nil, nil)

	// fmt.Printf("From party1: k1 : %x\n", p1.k1)
	// rfc6979.generateSecret(curve.N, x1, sha256.New(), h[:], func(k *big.Int) bool {
	// 	p1.k1 = k
	// 	return true
	// })

	// random generate k1, k=k1*k2
	// p1.k1 = crypto.RandomNum(curve.N)
	R2 := curves.ScalarToPoint(curve, p2.k2)

	proof, err := schnorr.ProveWithId(p2.sessionID, p2.k2, R2)
	if err != nil {
		return nil, nil, err
	}
	return proof, R2, nil
}

// Step2 paillier encrypt compute, return E[(h+xr)/k2]
func (p2 *P2Context) Step2(cmtD *commitment.Witness, p1Proof *schnorr.Proof) (*big.Int, error) {
	q := curve.N
	// check R1=k1*G commitment
	commit := commitment.HashCommitment{}
	commit.C = *p2.cmtC
	commit.Msg = *cmtD
	ok, commitD := commit.Open()
	if !ok {
		return nil, fmt.Errorf("commitment DeCommit fail")
	}
	if commitD[0].Cmp(p2.sessionID) != 0 {
		return nil, fmt.Errorf("p2 Step2 commitment sessionId error")
	}
	R1, err := curves.NewECPoint(curve, commitD[1], commitD[2])
	if err != nil {
		return nil, err
	}
	verify := schnorr.VerifyWithId(p2.sessionID, p1Proof, R1)
	if !verify {
		return nil, fmt.Errorf("schnorr verify fail")
	}
	// R = k1*k2*G, k = k1*k2
	Rx, _ := curve.ScalarMult(R1.X, R1.Y, p2.k2.Bytes())
	r := new(big.Int).Mod(Rx, q)
	bytes, err := hex.DecodeString(p2.message)
	if err != nil {
		return nil, err
	}
	k2_1 := new(big.Int).ModInverse(p2.k2, q)

	h := CalculateM(bytes)
	h = new(big.Int).Mul(h, k2_1) // h/k2

	rho := crypto.RandomNum(new(big.Int).Mul(q, q))
	rhoq := new(big.Int).Mul(rho, q)
	h_rhoq := new(big.Int).Add(h, rhoq) // h/k2 + rho*q

	E_x, err := p2.paiPub.HomoAddPlain(p2.E_x1, p2.x2)
	if err != nil {
		return nil, err
	}
	r = new(big.Int).Mul(r, k2_1) //  r/k2
	E_xr, err := p2.paiPub.HomoMulPlain(E_x, r)
	if err != nil {
		return nil, err
	}
	E_k2_h_xr, err := p2.paiPub.HomoAddPlain(E_xr, h_rhoq)
	if err != nil {
		return nil, err
	}
	return E_k2_h_xr, nil
}

func CalculateM(hash []byte) *big.Int {
	orderBits := curve.N.BitLen()
	orderBytes := (orderBits + 7) / 8
	if len(hash) > orderBytes {
		hash = hash[:orderBytes]
	}
	ret := new(big.Int).SetBytes(hash)
	excess := len(hash)*8 - orderBits
	if excess > 0 {
		ret.Rsh(ret, uint(excess))
	}
	return ret
}
