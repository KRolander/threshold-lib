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
New extentions :
	* Step1_with_rfc6979(...) deterministic signature
	* Step3_with_Recoveryid(...) returns r,s and the recovery id
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

var (
	curve = secp256k1.S256()
)

type P1Context struct {
	sessionID *big.Int

	publicKey *ecdsa.PublicKey
	paiPriKey *paillier.PrivateKey

	k1      *big.Int
	message string
	R2      *curves.ECPoint // k2*G
	cmtD    *commitment.Witness
}

// NewP1 2-party signature, P1 init
func NewP1(publicKey *ecdsa.PublicKey, message string, paiPriKey *paillier.PrivateKey) *P1Context {
	msg, err := hex.DecodeString(message)
	if err != nil {
		return nil
	}
	data := new(big.Int).SetBytes(msg)
	sessionId := crypto.SHA256Int(publicKey.X, publicKey.Y, data)

	p1Context := &P1Context{
		publicKey: publicKey,
		message:   message,
		paiPriKey: paiPriKey,
		sessionID: sessionId,
	}
	return p1Context
}

func (p1 *P1Context) Step1() (*commitment.Commitment, error) {
	if BanSignList.Has(hex.EncodeToString(p1.publicKey.X.Bytes())) {
		return nil, fmt.Errorf("ecdsa sign forbidden, publicKey " + hex.EncodeToString(p1.publicKey.X.Bytes()))
	}
	// random generate k1, k=k1*k2
	p1.k1 = crypto.RandomNum(curve.N)
	R1 := curves.ScalarToPoint(curve, p1.k1)
	cmt := commitment.NewCommitment(p1.sessionID, R1.X, R1.Y)
	p1.cmtD = &cmt.Msg
	return &cmt.C, nil
}

func (p1 *P1Context) Step1_with_rfc6979(x1 *big.Int) (*commitment.Commitment, error) {
	if BanSignList.Has(hex.EncodeToString(p1.publicKey.X.Bytes())) {
		return nil, fmt.Errorf("ecdsa sign forbidden, publicKey " + hex.EncodeToString(p1.publicKey.X.Bytes()))
	}

	msg, _ := hex.DecodeString(p1.message)

	h := sha256.Sum256(msg)

	p1.k1 = secp256k1.NonceRFC6979(x1, h[:], nil, nil)

	fmt.Printf("From party1: k1 : %x\n", p1.k1)
	// rfc6979.generateSecret(curve.N, x1, sha256.New(), h[:], func(k *big.Int) bool {
	// 	p1.k1 = k
	// 	return true
	// })

	// random generate k1, k=k1*k2
	// p1.k1 = crypto.RandomNum(curve.N)
	R1 := curves.ScalarToPoint(curve, p1.k1)

	cmt := commitment.NewCommitment(p1.sessionID, R1.X, R1.Y)
	p1.cmtD = &cmt.Msg
	return &cmt.C, nil
}

func (p1 *P1Context) Step2(p2Proof *schnorr.Proof, R2 *curves.ECPoint) (*schnorr.Proof, *commitment.Witness, error) {
	// zk schnorr verify k2
	verify := schnorr.VerifyWithId(p1.sessionID, p2Proof, R2)
	if !verify {
		return nil, nil, fmt.Errorf("schnorr verify fail")
	}
	p1.R2 = R2
	// zk schnorr prove k1
	R1 := curves.ScalarToPoint(curve, p1.k1)
	proof, err := schnorr.ProveWithId(p1.sessionID, p1.k1, R1)
	if err != nil {
		return nil, nil, err
	}
	return proof, p1.cmtD, nil
}

func (p1 *P1Context) Step3(E_k2_h_xr *big.Int) (*big.Int, *big.Int, error) {
	q := curve.N
	// R = k1*k2*G, k = k1*k2
	Rx, _ := curve.ScalarMult(p1.R2.X, p1.R2.Y, p1.k1.Bytes())
	r := new(big.Int).Mod(Rx, q)
	// paillier Decrypt (h+xr)/k2
	k2_h_xr, err := p1.paiPriKey.Decrypt(E_k2_h_xr)
	if err != nil {
		return nil, nil, err
	}
	k1_1 := new(big.Int).ModInverse(p1.k1, q)
	// s = (h+r*(x1+x2))/(k1*k2)
	s := new(big.Int).Mod(new(big.Int).Mul(k2_h_xr, k1_1), q)

	halfOrder := new(big.Int).Rsh(q, 1)
	if s.Cmp(halfOrder) == 1 {
		s.Sub(q, s)
	}
	if s.Sign() == 0 {
		return nil, nil, fmt.Errorf("calculated S is zero")
	}
	message, err := hex.DecodeString(p1.message)
	if err != nil {
		return nil, nil, err
	}
	// check ecdsa signature
	ok := ecdsa.Verify(p1.publicKey, message, r, s)
	if !ok {
		// IMPORTANT: If Verify fails, actively disallow signing to prevent attacks described in CVE-2023-33242
		BanSignList.Add(hex.EncodeToString(p1.publicKey.X.Bytes()))
		return nil, nil, fmt.Errorf("ecdsa sign verify fail")
	}
	return r, s, nil
}

func (p1 *P1Context) Step3_with_Recoveryid(E_k2_h_xr *big.Int) (*big.Int, *big.Int, uint8, error) {
	q := curve.N
	recid := uint8(0x0)
	recid_cond1 := uint8(0x0)
	recid_cond2 := uint8(0x0)

	// R = k1*k2*G, k = k1*k2
	Rx, Ry := curve.ScalarMult(p1.R2.X, p1.R2.Y, p1.k1.Bytes())
	// Process recovery id

	comparex := Rx.Cmp(q)
	if comparex == -1 {
		recid_cond1 = 0
	} else if comparex == 1 {
		recid_cond1 = 2
	}

	evenOrodd := Ry.Bit(0)
	if evenOrodd == 0 {
		// even
		recid_cond2 = 0
	} else {
		// Odd
		recid_cond2 = 1
	}
	recid = recid_cond1 | recid_cond2

	r := new(big.Int).Mod(Rx, q)
	// paillier Decrypt (h+xr)/k2
	k2_h_xr, err := p1.paiPriKey.Decrypt(E_k2_h_xr)
	if err != nil {
		return nil, nil, 0x0, err
	}
	k1_1 := new(big.Int).ModInverse(p1.k1, q)
	// s = (h+r*(x1+x2))/(k1*k2)
	s := new(big.Int).Mod(new(big.Int).Mul(k2_h_xr, k1_1), q)

	halfOrder := new(big.Int).Rsh(q, 1)
	if s.Cmp(halfOrder) == 1 {
		s.Sub(q, s)
		recid ^= 1
	}
	if s.Sign() == 0 {
		return nil, nil, 0x0, fmt.Errorf("calculated S is zero")
	}
	message, err := hex.DecodeString(p1.message)
	if err != nil {
		return nil, nil, 0x0, err
	}
	// check ecdsa signature
	ok := ecdsa.Verify(p1.publicKey, message, r, s)
	if !ok {
		// IMPORTANT: If Verify fails, actively disallow signing to prevent attacks described in CVE-2023-33242
		BanSignList.Add(hex.EncodeToString(p1.publicKey.X.Bytes()))
		return nil, nil, 0x0, fmt.Errorf("ecdsa sign verify fail")
	}

	return r, s, recid, nil
}
