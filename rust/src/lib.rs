// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![cfg_attr(not(feature = "std"), no_std)]
// #![warn(missing_docs)]

//! This crate implements a simple Sparse Merkle Tree utilities required for inter-op with Ethereum
//! bridge & Solidity contract.
//!
//! The implementation is optimised for usage within Substrate Runtime and supports no-std
//! compilation targets.
//!
//! Sparse Merkle Tree is constructed from 2^n length leaves, that are initially hashed using the
//! same [Hasher] as the inner nodes.
//! Inner nodes are created by concatenating child hashes and hashing again. The implementation
//! does not perform any sorting of the input data (leaves) nor when inner nodes are created.

#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

/// Supported hashing output size.
///
/// The size is restricted to 32 bytes to allow for a more optimised implementation.
pub type Hash = [u8; 32];

/// Generic hasher trait.
///
/// Implement the function to support custom way of hashing data.
/// The implementation must return a [Hash](type@Hash) type, so only 32-byte output hashes are
/// supported.
pub trait Hasher {
    /// Hash given arbitrary-length piece of data.
    fn hash(data: &[u8]) -> Hash;
}

#[cfg(feature = "keccak")]
mod keccak256 {
    use tiny_keccak::{Hasher as _, Keccak};

    /// Keccak256 hasher implementation.
    pub struct Keccak256;
    impl Keccak256 {
        /// Hash given data.
        pub fn hash(data: &[u8]) -> super::Hash {
            <Keccak256 as super::Hasher>::hash(data)
        }
    }
    impl super::Hasher for Keccak256 {
        fn hash(data: &[u8]) -> super::Hash {
            let mut keccak = Keccak::v256();
            keccak.update(data);
            let mut output = [0_u8; 32];
            keccak.finalize(&mut output);
            output
        }
    }
}
#[cfg(feature = "keccak")]
pub use keccak256::Keccak256;

pub fn merkle_tree<H, I, L>(leaves: I) -> Vec<Hash>
where
    H: Hasher,
    I: IntoIterator<Item = L>,
    L: AsRef<[u8]>,
{
    let mut leafs: Vec<Hash> = leaves.into_iter().map(|l| hash_leaf::<H, L>(l)).collect();
    let len = leafs.len();
    if len == 0 {
        return vec![Hash::default(), Hash::default()];
    }
    let num_leaves = round_up_to_pow2(len);
    if num_leaves > len {
        let emtpy = vec![Hash::default(); num_leaves - len];
        leafs.extend(emtpy);
    }
    let depth = log2(num_leaves);

    #[cfg(feature = "debug")]
    log::debug!("{:?}", usize::pow(2, depth.try_into().unwrap()));
    log::debug!("{:?}", num_leaves);

    assert_eq!(num_leaves, usize::pow(2, depth.try_into().unwrap()));
    let num_nodes = 2 * num_leaves;
    let mut tree = vec![Hash::default(); num_nodes];
    tree[num_leaves..(num_leaves + num_leaves)].clone_from_slice(&leafs[..num_leaves]);
    for i in (1..num_leaves).rev() {
        let left = tree[2 * i];
        let right = tree[2 * i + 1];

        #[cfg(feature = "debug")]
        log::debug!("index: {:?}", &i);
        log::debug!(" left: {:?}", hex::encode(left));
        log::debug!("right: {:?}", hex::encode(right));

        tree[i] = hash_node::<H>(left, right);
    }
    tree
}

pub fn merkle_root(tree: Vec<Hash>) -> Hash {
    tree[1]
}

#[derive(Debug, PartialEq, Eq)]
pub struct MerkleProof<T> {
    pub root: Hash,
    pub proof: Vec<Hash>,
    pub depth: usize,
    pub indices: Vec<usize>,
    pub leaves: Vec<T>,
}

pub fn merkle_proof<H, I, T>(leaves: I, indices: Vec<usize>) -> MerkleProof<T>
where
    H: Hasher,
    I: IntoIterator<Item = T> + Clone,
    I::IntoIter: ExactSizeIterator,
    T: AsRef<[u8]> + Clone,
{
    let mut m_indices: Vec<usize> = indices.to_vec();
    m_indices.sort_by(|a, b| b.cmp(a));
    let tree = merkle_tree::<H, I, T>(leaves.clone());
    let depth = log2(tree.len()) - 1;
    let num_leaves = usize::pow(2, depth.try_into().unwrap());
    let num_nodes = 2 * num_leaves;
    let mut known = vec![false; num_nodes];
    let mut decommitment: Vec<Hash> = vec![];
    for i in m_indices.clone() {
        known[num_leaves + i] = true;
    }
    for i in (1..num_leaves).rev() {
        let left = known[2 * i];
        let right = known[2 * i + 1];
        if left && !right {
            decommitment.push(tree[2 * i + 1]);
        }
        if !left && right {
            decommitment.push(tree[2 * i]);
        }
        known[i] = left | right;
    }
    let root = merkle_root(tree);
    let mut index_leaves: Vec<T> = vec![];
    let leafs: Vec<T> = leaves.into_iter().collect();
    for i in m_indices.clone() {
        let l = leafs[i].clone();
        index_leaves.push(l);
    }

    #[cfg(feature = "debug")]
    log::debug!(
        "[merkle_proof] Proof: {:?}",
        decommitment.iter().map(hex::encode).collect::<Vec<_>>()
    );

    MerkleProof {
        root,
        proof: decommitment,
        depth,
        indices: m_indices,
        leaves: index_leaves,
    }
}

pub fn verify_proof<H, L>(
    root: Hash,
    depth: usize,
    indices: Vec<usize>,
    proof: Vec<Hash>,
    leaves: Vec<L>,
) -> bool
where
    H: Hasher,
    L: AsRef<[u8]>,
{
    let mut queue: Vec<(usize, Hash)> = vec![];
    let num_leaves = usize::pow(2, depth.try_into().unwrap());
    let _ = indices
        .iter()
        .enumerate()
        .map(|(i, idx)| {
            let tree_index = num_leaves + idx;
            let hash = H::hash(leaves[i].as_ref());
            queue.push((tree_index, hash));
        })
        .collect::<Vec<_>>();
    if queue.is_empty() {
        return false;
    }
    let mut decommitment = proof.to_vec();
    loop {
        let (index, hash) = queue.remove(0);

        #[cfg(feature = "debug")]
        log::debug!(
            "[verify_proof] index: {:?}, hash: {:?}",
            index,
            hex::encode(hash)
        );

        if index == 1 {
            return root == hash;
        } else if index % 2 == 0 {
            if decommitment.is_empty() {
                return false;
            }
            queue.push((index / 2, hash_node::<H>(hash, decommitment[0])));
            decommitment.remove(0);
        } else if !queue.is_empty() && queue[0].0 == index - 1 {
            let (_, sibbling_hash) = queue.remove(0);
            queue.push((index / 2, hash_node::<H>(sibbling_hash, hash)));
        } else {
            if decommitment.is_empty() {
                return false;
            }
            queue.push((index / 2, hash_node::<H>(decommitment[0], hash)));
            decommitment.remove(0);
        }
    }
}

fn hash_leaf<H, L>(leaf: L) -> Hash
where
    H: Hasher,
    L: AsRef<[u8]>,
{
    H::hash(leaf.as_ref())
}

fn hash_node<H>(left: Hash, right: Hash) -> Hash
where
    H: Hasher,
{
    let mut combined = [0_u8; 64];
    combined[0..32].copy_from_slice(&left);
    combined[32..64].copy_from_slice(&right);
    H::hash(&combined)
}

fn log2(x: usize) -> usize {
    if 1 == x {
        0
    } else {
        1 + log2(x / 2)
    }
}

fn round_up_to_pow2(x: usize) -> usize {
    if x <= 1 {
        1
    } else {
        2 * round_up_to_pow2((x + 1) / 2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use hex_literal::hex;

    #[test]
    fn should_generate_empty_root() {
        // given
        let _ = env_logger::try_init();
        let data: Vec<[u8; 1]> = Default::default();

        // when
        let tree = merkle_tree::<Keccak256, _, _>(data);
        let out = merkle_root(tree);

        // then
        assert_eq!(
            hex::encode(&out),
            "0000000000000000000000000000000000000000000000000000000000000000"
        );
    }

    #[test]
    fn should_generate_single_root() {
        // given
        let _ = env_logger::try_init();
        let data = vec![hex!("E04CC55ebEE1cBCE552f250e85c57B70B2E2625b")];

        // when
        let tree = merkle_tree::<Keccak256, _, _>(data);
        let out = merkle_root(tree);

        // then
        assert_eq!(
            hex::encode(&out),
            "aeb47a269393297f4b0a3c9c9cfd00c7a4195255274cf39d83dabc2fcc9ff3d7"
        );
    }

    #[test]
    fn should_generate_root_pow_2() {
        // given
        let _ = env_logger::try_init();
        let data = vec![
            hex!("E04CC55ebEE1cBCE552f250e85c57B70B2E2625b"),
            hex!("25451A4de12dcCc2D166922fA938E900fCc4ED24"),
        ];

        // when
        let tree = merkle_tree::<Keccak256, _, _>(data);
        let out = merkle_root(tree);

        // then
        assert_eq!(
            hex::encode(&out),
            "697ea2a8fe5b03468548a7a413424a6292ab44a82a6f5cc594c3fa7dda7ce402"
        );
    }

    #[test]
    fn should_generate_root_complex() {
        let _ = env_logger::try_init();
        let test = |root, data| {
            let tree = merkle_tree::<Keccak256, _, _>(data);
            assert_eq!(hex::encode(&merkle_root(tree)), root);
        };

        test(
            "bb7435dc6d054fe2f2d80bc6d511c4ee773787506cb84b59f9f3f3ed2d9f7a90",
            vec!["a", "b", "c"],
        );

        test(
            "743e302e07426aa259113f60de5d0146db96da26620fbbe53533a60c695899db",
            vec!["a", "b", "a"],
        );

        test(
            "dc8e73fe6903148ff5079baecc043983625c23b39f31537e322cd0deee09fa9c",
            vec!["a", "b", "a", "b"],
        );

        test(
            "5befebdcc0e1a7159daeb02385e09e2fc1ebf151e42d8d1591601e1f92e5b217",
            vec!["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"],
        );
    }

    #[test]
    fn should_generate_and_verify_proof_simple() {
        // given
        let _ = env_logger::try_init();
        let data = vec!["a", "b", "c"];

        // when
        let proof0 = merkle_proof::<Keccak256, _, _>(data.clone(), vec![0]);
        assert!(verify_proof::<Keccak256, _>(
            proof0.root,
            proof0.depth,
            proof0.indices.clone(),
            proof0.proof.clone(),
            proof0.leaves.clone(),
        ));

        let proof1 = merkle_proof::<Keccak256, _, _>(data.clone(), vec![1]);
        assert!(verify_proof::<Keccak256, _>(
            proof1.root,
            proof1.depth,
            proof1.indices,
            proof1.proof,
            proof1.leaves,
        ));
        let proof2 = merkle_proof::<Keccak256, _, _>(data.clone(), vec![2]);
        assert!(verify_proof::<Keccak256, _>(
            proof2.root,
            proof2.depth,
            proof2.indices,
            proof2.proof,
            proof2.leaves,
        ));

        let proof3 = merkle_proof::<Keccak256, _, _>(data.clone(), vec![0, 1]);
        log::debug!("{:?}", proof3);
        assert!(verify_proof::<Keccak256, _>(
            proof3.root,
            proof3.depth,
            proof3.indices,
            proof3.proof,
            proof3.leaves,
        ));

        let proof4 = merkle_proof::<Keccak256, _, _>(data.clone(), vec![0, 2]);
        assert!(verify_proof::<Keccak256, _>(
            proof4.root,
            proof4.depth,
            proof4.indices,
            proof4.proof,
            proof4.leaves,
        ));

        let proof5 = merkle_proof::<Keccak256, _, _>(data.clone(), vec![1, 2]);
        assert!(verify_proof::<Keccak256, _>(
            proof5.root,
            proof5.depth,
            proof5.indices,
            proof5.proof,
            proof5.leaves,
        ));

        let proof6 = merkle_proof::<Keccak256, _, _>(data.clone(), vec![0, 1, 2]);
        assert!(verify_proof::<Keccak256, _>(
            proof6.root,
            proof6.depth,
            proof6.indices,
            proof6.proof,
            proof6.leaves,
        ));

        // then
        assert_eq!(hex::encode(proof0.root), hex::encode(proof1.root));
        assert_eq!(hex::encode(proof2.root), hex::encode(proof1.root));
        assert_eq!(hex::encode(proof3.root), hex::encode(proof1.root));
        assert_eq!(hex::encode(proof4.root), hex::encode(proof1.root));
        assert_eq!(hex::encode(proof5.root), hex::encode(proof1.root));
        assert_eq!(hex::encode(proof6.root), hex::encode(proof1.root));

        let proof = merkle_proof::<Keccak256, _, _>(data.clone(), vec![]);
        log::debug!("{:?}", proof);
        assert!(!verify_proof::<Keccak256, _>(
            proof.root,
            proof.depth,
            proof.indices.clone(),
            proof.proof.clone(),
            proof.leaves.clone(),
        ));

        assert!(!verify_proof::<Keccak256, _>(
            hex!("ab7435dc6d054fe2f2d80bc6d511c4ee773787506cb84b59f9f3f3ed2d9f7a90"),
            proof0.depth,
            proof0.indices.clone(),
            proof0.proof.clone(),
            proof0.leaves.clone(),
        ));

        assert!(!verify_proof::<Keccak256, _>(
            proof0.root,
            proof0.depth,
            proof0.indices,
            vec![],
            proof0.leaves,
        ));
    }

    #[test]
    fn should_generate_and_verify_proof_complex() {
        fn powerset(s: &[usize]) -> Vec<Vec<usize>> {
            let mut subsets: Vec<Vec<usize>> = vec![];
            let empty: Vec<usize> = vec![];
            subsets.push(empty);
            let mut updated: Vec<Vec<usize>> = vec![];
            for ele in s {
                for mut sub in subsets.clone() {
                    sub.push(*ele);
                    updated.push(sub);
                }
                subsets.append(&mut updated);
            }
            subsets
        }

        // given
        let _ = env_logger::try_init();
        let data = vec!["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"];
        let mut v = vec![];
        for l in 0..data.len() {
            v.push(l);
        }
        let subsets = powerset(&v);
        for indices in subsets {
            if !indices.is_empty() {
                // when
                let proof = merkle_proof::<Keccak256, _, _>(data.clone(), indices);
                // then
                assert!(verify_proof::<Keccak256, _>(
                    proof.root,
                    proof.depth,
                    proof.indices,
                    proof.proof,
                    proof.leaves
                ));
            }
        }
    }

    #[test]
    fn should_generate_and_verify_proof_large() {
        // given
        let _ = env_logger::try_init();
        let mut data = vec![];
        for i in 1..16 {
            for c in 'a'..'z' {
                if c as usize % i != 0 {
                    data.push(c.to_string());
                }
            }

            for l in 0..data.len() {
                // when
                let proof = merkle_proof::<Keccak256, _, _>(data.clone(), vec![l]);
                // then
                assert!(verify_proof::<Keccak256, _>(
                    proof.root,
                    proof.depth,
                    proof.indices,
                    proof.proof,
                    proof.leaves,
                ));
            }
        }
    }

    #[test]
    fn should_generate_and_verify_proof_large_tree() {
        // given
        let _ = env_logger::try_init();
        let mut data = vec![];
        for i in 0..6000 {
            data.push(format!("{}", i));
        }

        for l in (0..data.len()).step_by(13) {
            // when
            let proof = merkle_proof::<Keccak256, _, _>(data.clone(), vec![l]);
            // then
            assert!(verify_proof::<Keccak256, _>(
                proof.root,
                proof.depth,
                proof.indices,
                proof.proof,
                proof.leaves
            ));
        }
    }

    #[test]
    #[should_panic]
    fn should_panic_on_invalid_leaf_index() {
        let _ = env_logger::try_init();
        merkle_proof::<Keccak256, _, _>(vec!["a"], vec![5]);
    }

    #[test]
    fn should_generate_and_verify_proof_on_test_data() {
        let _ = env_logger::try_init();
        let addresses = vec![
            "0x9aF1Ca5941148eB6A3e9b9C741b69738292C533f",
            "0xDD6ca953fddA25c496165D9040F7F77f75B75002",
            "0x60e9C47B64Bc1C7C906E891255EaEC19123E7F42",
            "0xfa4859480Aa6D899858DE54334d2911E01C070df",
            "0x19B9b128470584F7209eEf65B69F3624549Abe6d",
            "0xC436aC1f261802C4494504A11fc2926C726cB83b",
            "0xc304C8C2c12522F78aD1E28dD86b9947D7744bd0",
            "0xDa0C2Cba6e832E55dE89cF4033affc90CC147352",
            "0xf850Fd22c96e3501Aad4CDCBf38E4AEC95622411",
            "0x684918D4387CEb5E7eda969042f036E226E50642",
            "0x963F0A1bFbb6813C0AC88FcDe6ceB96EA634A595",
            "0x39B38ad74b8bCc5CE564f7a27Ac19037A95B6099",
            "0xC2Dec7Fdd1fef3ee95aD88EC8F3Cd5bd4065f3C7",
            "0x9E311f05c2b6A43C2CCF16fB2209491BaBc2ec01",
            "0x927607C30eCE4Ef274e250d0bf414d4a210b16f0",
            "0x98882bcf85E1E2DFF780D0eB360678C1cf443266",
            "0xFBb50191cd0662049E7C4EE32830a4Cc9B353047",
            "0x963854fc2C358c48C3F9F0A598B9572c581B8DEF",
            "0xF9D7Bc222cF6e3e07bF66711e6f409E51aB75292",
            "0xF2E3fd32D063F8bBAcB9e6Ea8101C2edd899AFe6",
            "0x407a5b9047B76E8668570120A96d580589fd1325",
            "0xEAD9726FAFB900A07dAd24a43AE941d2eFDD6E97",
            "0x42f5C8D9384034A9030313B51125C32a526b6ee8",
            "0x158fD2529Bc4116570Eb7C80CC76FEf33ad5eD95",
            "0x0A436EE2E4dEF3383Cf4546d4278326Ccc82514E",
            "0x34229A215db8FeaC93Caf8B5B255e3c6eA51d855",
            "0xEb3B7CF8B1840242CB98A732BA464a17D00b5dDF",
            "0x2079692bf9ab2d6dc7D79BBDdEE71611E9aA3B72",
            "0x46e2A67e5d450e2Cf7317779f8274a2a630f3C9B",
            "0xA7Ece4A5390DAB18D08201aE18800375caD78aab",
            "0x15E1c0D24D62057Bf082Cb2253dA11Ef0d469570",
            "0xADDEF4C9b5687Eb1F7E55F2251916200A3598878",
            "0xe0B16Fb96F936035db2b5A68EB37D470fED2f013",
            "0x0c9A84993feaa779ae21E39F9793d09e6b69B62D",
            "0x3bc4D5148906F70F0A7D1e2756572655fd8b7B34",
            "0xFf4675C26903D5319795cbd3a44b109E7DDD9fDe",
            "0xCec4450569A8945C6D2Aba0045e4339030128a92",
            "0x85f0584B10950E421A32F471635b424063FD8405",
            "0xb38bEe7Bdc0bC43c096e206EFdFEad63869929E3",
            "0xc9609466274Fef19D0e58E1Ee3b321D5C141067E",
            "0xa08EA868cF75268E7401021E9f945BAe73872ecc",
            "0x67C9Cb1A29E964Fe87Ff669735cf7eb87f6868fE",
            "0x1B6BEF636aFcdd6085cD4455BbcC93796A12F6E2",
            "0x46B37b243E09540b55cF91C333188e7D5FD786dD",
            "0x8E719E272f62Fa97da93CF9C941F5e53AA09e44a",
            "0xa511B7E7DB9cb24AD5c89fBb6032C7a9c2EfA0a5",
            "0x4D11FDcAeD335d839132AD450B02af974A3A66f8",
            "0xB8cf790a5090E709B4619E1F335317114294E17E",
            "0x7f0f57eA064A83210Cafd3a536866ffD2C5eDCB3",
            "0xC03C848A4521356EF800e399D889e9c2A25D1f9E",
            "0xC6b03DF05cb686D933DD31fCa5A993bF823dc4FE",
            "0x58611696b6a8102cf95A32c25612E4cEF32b910F",
            "0x2ed4bC7197AEF13560F6771D930Bf907772DE3CE",
            "0x3C5E58f334306be029B0e47e119b8977B2639eb4",
            "0x288646a1a4FeeC560B349d210263c609aDF649a6",
            "0xb4F4981E0d027Dc2B3c86afA0D0fC03d317e83C0",
            "0xaAE4A87F8058feDA3971f9DEd639Ec9189aA2500",
            "0x355069DA35E598913d8736E5B8340527099960b8",
            "0x3cf5A0F274cd243C0A186d9fCBdADad089821B93",
            "0xca55155dCc4591538A8A0ca322a56EB0E4aD03C4",
            "0xE824D0268366ec5C4F23652b8eD70D552B1F2b8B",
            "0x84C3e9B25AE8a9b39FF5E331F9A597F2DCf27Ca9",
            "0xcA0018e278751De10d26539915d9c7E7503432FE",
            "0xf13077dE6191D6c1509ac7E088b8BE7Fe656c28b",
            "0x7a6bcA1ec9Db506e47ac6FD86D001c2aBc59C531",
            "0xeA7f9A2A9dd6Ba9bc93ca615C3Ddf26973146911",
            "0x8D0d8577e16F8731d4F8712BAbFa97aF4c453458",
            "0xB7a7855629dF104246997e9ACa0E6510df75d0ea",
            "0x5C1009BDC70b0C8Ab2e5a53931672ab448C17c89",
            "0x40B47D1AfefEF5eF41e0789F0285DE7b1C31631C",
            "0x5086933d549cEcEB20652CE00973703CF10Da373",
            "0xeb364f6FE356882F92ae9314fa96116Cf65F47d8",
            "0xdC4D31516A416cEf533C01a92D9a04bbdb85EE67",
            "0x9b36E086E5A274332AFd3D8509e12ca5F6af918d",
            "0xBC26394fF36e1673aE0608ce91A53B9768aD0D76",
            "0x81B5AB400be9e563fA476c100BE898C09966426c",
            "0x9d93C8ae5793054D28278A5DE6d4653EC79e90FE",
            "0x3B8E75804F71e121008991E3177fc942b6c28F50",
            "0xC6Eb5886eB43dD473f5BB4e21e56E08dA464D9B4",
            "0xfdf1277b71A73c813cD0e1a94B800f4B1Db66DBE",
            "0xc2ff2cCc98971556670e287Ff0CC39DA795231ad",
            "0x76b7E1473f0D0A87E9B4a14E2B179266802740f5",
            "0xA7Bc965660a6EF4687CCa4F69A97563163A3C2Ef",
            "0xB9C2b47888B9F8f7D03dC1de83F3F55E738CebD3",
            "0xEd400162E6Dd6bD2271728FFb04176bF770De94a",
            "0xE3E8331156700339142189B6E555DCb2c0962750",
            "0xbf62e342Bc7706a448EdD52AE871d9C4497A53b1",
            "0xb9d7A1A111eed75714a0AcD2dd467E872eE6B03D",
            "0x03942919DFD0383b8c574AB8A701d89fd4bfA69D",
            "0x0Ef4C92355D3c8c7050DFeb319790EFCcBE6fe9e",
            "0xA6895a3cf0C60212a73B3891948ACEcF1753f25E",
            "0x0Ed509239DB59ef3503ded3d31013C983d52803A",
            "0xc4CE8abD123BfAFc4deFf37c7D11DeCd5c350EE4",
            "0x4A4Bf59f7038eDcd8597004f35d7Ee24a7Bdd2d3",
            "0x5769E8e8A2656b5ed6b6e6fa2a2bFAeaf970BB87",
            "0xf9E15cCE181332F4F57386687c1776b66C377060",
            "0xc98f8d4843D56a46C21171900d3eE538Cc74dbb5",
            "0x3605965B47544Ce4302b988788B8195601AE4dEd",
            "0xe993BDfdcAac2e65018efeE0F69A12678031c71d",
            "0x274fDf8801385D3FAc954BCc1446Af45f5a8304c",
            "0xBFb3f476fcD6429F4a475bA23cEFdDdd85c6b964",
            "0x806cD16588Fe812ae740e931f95A289aFb4a4B50",
            "0xa89488CE3bD9C25C3aF797D1bbE6CA689De79d81",
            "0xd412f1AfAcf0Ebf3Cd324593A231Fc74CC488B12",
            "0xd1f715b2D7951d54bc31210BbD41852D9BF98Ed1",
            "0xf65aD707c344171F467b2ADba3d14f312219cE23",
            "0x2971a4b242e9566dEF7bcdB7347f5E484E11919B",
            "0x12b113D6827E07E7D426649fBd605f427da52314",
            "0x1c6CA45171CDb9856A6C9Dba9c5F1216913C1e97",
            "0x11cC6ee1d74963Db23294FCE1E3e0A0555779CeA",
            "0x8Aa1C721255CDC8F895E4E4c782D86726b068667",
            "0xA2cDC1f37510814485129aC6310b22dF04e9Bbf0",
            "0xCf531b71d388EB3f5889F1f78E0d77f6fb109767",
            "0xBe703e3545B2510979A0cb0C440C0Fba55c6dCB5",
            "0x30a35886F989db39c797D8C93880180Fdd71b0c8",
            "0x1071370D981F60c47A9Cd27ac0A61873a372cBB2",
            "0x3515d74A11e0Cb65F0F46cB70ecf91dD1712daaa",
            "0x50500a3c2b7b1229c6884505D00ac6Be29Aecd0C",
            "0x9A223c2a11D4FD3585103B21B161a2B771aDA3d1",
            "0xd7218df03AD0907e6c08E707B15d9BD14285e657",
            "0x76CfD72eF5f93D1a44aD1F80856797fBE060c70a",
            "0x44d093cB745944991EFF5cBa151AA6602d6f5420",
            "0x626516DfF43bf09A71eb6fd1510E124F96ED0Cde",
            "0x6530824632dfe099304E2DC5701cA99E6d031E08",
            "0x57e6c423d6a7607160d6379A0c335025A14DaFC0",
            "0x3966D4AD461Ef150E0B10163C81E79b9029E69c3",
            "0xF608aCfd0C286E23721a3c347b2b65039f6690F1",
            "0xbfB8FAac31A25646681936977837f7740fCd0072",
            "0xd80aa634a623a7ED1F069a1a3A28a173061705c7",
            "0x9122a77B36363e24e12E1E2D73F87b32926D3dF5",
            "0x62562f0d1cD31315bCCf176049B6279B2bfc39C2",
            "0x48aBF7A2a7119e5675059E27a7082ba7F38498b2",
            "0xb4596983AB9A9166b29517acD634415807569e5F",
            "0x52519D16E20BC8f5E96Da6d736963e85b2adA118",
            "0x7663893C3dC0850EfC5391f5E5887eD723e51B83",
            "0x5FF323a29bCC3B5b4B107e177EccEF4272959e61",
            "0xee6e499AdDf4364D75c05D50d9344e9daA5A9AdF",
            "0x1631b0BD31fF904aD67dD58994C6C2051CDe4E75",
            "0xbc208e9723D44B9811C428f6A55722a26204eEF2",
            "0xe76103a222Ee2C7Cf05B580858CEe625C4dc00E1",
            "0xC71Bb2DBC51760f4fc2D46D84464410760971B8a",
            "0xB4C18811e6BFe564D69E12c224FFc57351f7a7ff",
            "0xD11DB0F5b41061A887cB7eE9c8711438844C298A",
            "0xB931269934A3D4432c084bAAc3d0de8143199F4f",
            "0x070037cc85C761946ec43ea2b8A2d5729908A2a1",
            "0x2E34aa8C95Ffdbb37f14dCfBcA69291c55Ba48DE",
            "0x052D93e8d9220787c31d6D83f87eC7dB088E998f",
            "0x498dAC6C69b8b9ad645217050054840f1D91D029",
            "0xE4F7D60f9d84301e1fFFd01385a585F3A11F8E89",
            "0xEa637992f30eA06460732EDCBaCDa89355c2a107",
            "0x4960d8Da07c27CB6Be48a79B96dD70657c57a6bF",
            "0x7e471A003C8C9fdc8789Ded9C3dbe371d8aa0329",
            "0xd24265Cc10eecb9e8d355CCc0dE4b11C556E74D7",
            "0xDE59C8f7557Af779674f41CA2cA855d571018690",
            "0x2fA8A6b3b6226d8efC9d8f6EBDc73Ca33DDcA4d8",
            "0xe44102664c6c2024673Ff07DFe66E187Db77c65f",
            "0x94E3f4f90a5f7CBF2cc2623e66B8583248F01022",
            "0x0383EdBbc21D73DEd039E9C1Ff6bf56017b4CC40",
            "0x64C3E49898B88d1E0f0d02DA23E0c00A2Cd0cA99",
            "0xF4ccfB67b938d82B70bAb20975acFAe402E812E1",
            "0x4f9ee5829e9852E32E7BC154D02c91D8E203e074",
            "0xb006312eF9713463bB33D22De60444Ba95609f6B",
            "0x7Cbe76ef69B52110DDb2e3b441C04dDb11D63248",
            "0x70ADEEa65488F439392B869b1Df7241EF317e221",
            "0x64C0bf8AA36Ba590477585Bc0D2BDa7970769463",
            "0xA4cDc98593CE52d01Fe5Ca47CB3dA5320e0D7592",
            "0xc26B34D375533fFc4c5276282Fa5D660F3d8cbcB",
        ];
        let root = hex!("2cf28c36ec8bd4881881cc644a9fd4aade6b45989a73ab3fa7aebeacc46b6dbf");

        let data = addresses
            .into_iter()
            .map(|address| hex::decode(&address[2..]).unwrap())
            .collect::<Vec<_>>();

        for l in 0..data.len() {
            // when
            let proof = merkle_proof::<Keccak256, _, _>(data.clone(), vec![l]);
            assert_eq!(hex::encode(&proof.root), hex::encode(&root));
            assert_eq!(proof.indices[0], l);
            assert_eq!(proof.leaves[0], data[l]);

            // then
            assert!(verify_proof::<Keccak256, _>(
                proof.root,
                proof.depth,
                proof.indices,
                proof.proof,
                proof.leaves
            ));
        }

        let proof = merkle_proof::<Keccak256, _, _>(data.clone(), vec![data.len() - 1]);

        assert_eq!(
            proof,
            MerkleProof {
                root,
                depth: 8,
                indices: vec![data.len() - 1],
                proof: vec![
                    hex!("0000000000000000000000000000000000000000000000000000000000000000"),
                    hex!("340bcb1d49b2d82802ddbcf5b85043edb3427b65d09d7f758fbc76932ad2da2f"),
                    hex!("ba0580e5bd530bc93d61276df7969fb5b4ae8f1864b4a28c280249575198ff1f"),
                    hex!("21ddb9a356815c3fac1026b6dec5df3124afbadb485c9ba5a3e3398a04b7ba85"),
                    hex!("e58769b32a1beaf1ea27375a44095a0d1fb664ce2dd358e7fcbfb78c26a19344"),
                    hex!("d02609d2bbdb28aa25f58b85afec937d5a4c85d37925bce6d0cf802f9d76ba79"),
                    hex!("887c22bd8750d34016ac3c66b5ff102dacdd73f6b014e710b51e8022af9a1968"),
                    hex!("ae3f8991955ed884613b0a5f40295902eea0e0abe5858fc520b72959bc016d4e"),
                ],
                leaves: vec![hex!("c26B34D375533fFc4c5276282Fa5D660F3d8cbcB").to_vec()],
            }
        );
    }
}
