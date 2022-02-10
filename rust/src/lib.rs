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
    let leafs: Vec<Hash> = leaves.into_iter().map(|l| hash_leaf::<H, L>(l)).collect();
    let num_leaves = leafs.len();
    if num_leaves == 0 {
        return vec![Hash::default(), Hash::default()];
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
    T: AsRef<[u8]>,
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
    for i in (1..=num_leaves).rev() {
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
    let index_leaves = leaves
        .into_iter()
        .enumerate()
        .filter(|(idx, _)| m_indices.contains(idx))
        .map(|(_, v)| v)
        .collect();

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

pub fn verify_proof<H, P, L>(
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
    for index in indices {
        let tree_index = usize::pow(2, depth.try_into().unwrap());
        let hash = H::hash(leaves[index].as_ref());
        queue.push((tree_index, hash));
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
            queue.push((index / 2, hash_node::<H>(hash, decommitment[0])));
            decommitment.remove(0);
        } else if !queue.is_empty() && queue[0].0 == index - 1 {
            let (_, sibbling_hash) = queue.remove(0);
            queue.push((index / 2, hash_node::<H>(sibbling_hash, hash)));
        } else {
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
        let out = merkle_root::<Keccak256, _, _>(data);

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
        let mut data = vec![hex!("E04CC55ebEE1cBCE552f250e85c57B70B2E2625b")];
        data.push(hex!("0000000000000000000000000000000000000000"));

        // when
        let out = merkle_root::<Keccak256, _, _>(data);

        // then
        assert_eq!(
            hex::encode(&out),
            "db047d9da87be3331d28feb8d930b251283a6ab467a185d8c955be1241396f8c"
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
        let out = merkle_root::<Keccak256, _, _>(data);

        // then
        assert_eq!(
            hex::encode(&out),
            "697ea2a8fe5b03468548a7a413424a6292ab44a82a6f5cc594c3fa7dda7ce402"
        );
    }
}
