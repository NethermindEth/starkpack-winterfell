// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use super::Table;
use crypto::{BatchMerkleProof, ElementHasher, Hasher};
use math::FieldElement;
use utils::{
    collections::Vec, ByteReader, ByteWriter, Deserializable, DeserializationError, Serializable,
    SliceReader,
};

// QUERIES
// ================================================================================================
/// Decommitments to evaluations of a set of functions at multiple points.
///
/// Given a set of functions evaluated over a domain *D*, a commitment is assumed to be a Merkle
/// tree where a leaf at position *i* contains evaluations of all functions at *x<sub>i</sub>*.
/// Thus, a query (i.e. a single decommitment) for position *i* includes evaluations of all
/// functions at *x<sub>i</sub>*, accompanied by a Merkle authentication path from the leaf *i* to
/// the tree root.
///
/// This struct can contain one or more queries. In cases when more than one query is stored,
/// Merkle authentication paths are compressed to remove redundant nodes.
///
/// Internally, all Merkle paths and query values are stored as a sequence of bytes. Thus, to
/// retrieve query values and the corresponding Merkle authentication paths,
/// [parse()](Queries::parse) function should be used.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Queries {
    paths: Vec<u8>,
    values: Vec<u8>,
}

impl Queries {
    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    /// Returns queries constructed from evaluations of a set of functions at some number of points
    /// in a domain and their corresponding Merkle authentication paths.
    ///
    /// For each evaluation point, the same number of values must be provided, and a hash of
    /// these values must be equal to a leaf node in the corresponding Merkle authentication path.
    ///
    /// # Panics
    /// Panics if:
    /// * No queries were provided (`query_values` is an empty vector).
    /// * Any of the queries does not contain any evaluations.
    /// * Not all queries contain the same number of evaluations.
    pub fn new<H: Hasher, E: FieldElement>(
        merkle_proof: BatchMerkleProof<H>,
        query_values: Vec<Vec<E>>,
    ) -> Self {
        assert!(!query_values.is_empty(), "query values cannot be empty");
        let elements_per_query = query_values[0].len();
        assert_ne!(
            elements_per_query, 0,
            "a query must contain at least one evaluation"
        );

        // TODO: add debug check that values actually hash into the leaf nodes of the batch proof

        // concatenate all elements together into a single vector of bytes
        let num_queries = query_values.len();
        let mut values = Vec::with_capacity(num_queries * elements_per_query * E::ELEMENT_BYTES);
        for elements in query_values.iter() {
            assert_eq!(
                elements.len(),
                elements_per_query,
                "all queries must contain the same number of evaluations"
            );
            values.write(elements);
        }

        // serialize internal nodes of the batch Merkle proof; we care about internal nodes only
        // because leaf nodes can be reconstructed from hashes of query values
        let paths = merkle_proof.serialize_nodes();

        Queries { paths, values }
    }

    // PARSER
    // --------------------------------------------------------------------------------------------
    /// Convert internally stored bytes into a set of query values and the corresponding Merkle
    /// authentication paths.
    ///
    /// # Panics
    /// Panics if:
    /// * `domain_size` is not a power of two.
    /// * `num_queries` is zero.
    /// * `values_per_query` is zero.
    pub fn parse<H, E>(
        self,
        domain_size: usize,
        num_queries: usize,
        values_per_query: usize,
    ) -> Result<(BatchMerkleProof<H>, Table<E>), DeserializationError>
    where
        E: FieldElement,
        H: ElementHasher<BaseField = E::BaseField>,
    {
        assert!(
            domain_size.is_power_of_two(),
            "domain size must be a power of two"
        );
        assert!(num_queries > 0, "there must be at least one query");
        assert!(
            values_per_query > 0,
            "a query must contain at least one value"
        );

        // make sure we have enough bytes to read the expected number of queries
        let num_query_bytes = E::ELEMENT_BYTES * values_per_query;
        let expected_bytes = num_queries * num_query_bytes;
        if self.values.len() != expected_bytes {
            return Err(DeserializationError::InvalidValue(format!(
                "expected {} query value bytes, but was {}",
                expected_bytes,
                self.values.len()
            )));
        }

        // read bytes corresponding to each query, convert them into field elements,
        // and also hash them to build leaf nodes of the batch Merkle proof
        let query_values = Table::<E>::from_bytes(&self.values, num_queries, values_per_query)?;
        let hashed_queries = query_values
            .rows()
            .map(|row| H::hash_elements(row))
            .collect();

        // build batch Merkle proof
        let mut reader = SliceReader::new(&self.paths);
        let tree_depth = domain_size.ilog2() as u8;
        let merkle_proof = BatchMerkleProof::deserialize(&mut reader, hashed_queries, tree_depth)?;
        if reader.has_more_bytes() {
            return Err(DeserializationError::UnconsumedBytes);
        }

        Ok((merkle_proof, query_values))
    }
}

impl Serializable for Queries {
    /// Serializes `self` and writes the resulting bytes into the `target`.
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        // write value bytes
        target.write_u32(self.values.len() as u32);
        target.write_bytes(&self.values);

        // write path bytes
        target.write_u32(self.paths.len() as u32);
        target.write_bytes(&self.paths);
    }
}

impl Deserializable for Queries {
    /// Reads a query struct from the specified `source` and returns the result
    ///
    /// # Errors
    /// Returns an error of a valid query struct could not be read from the specified source.
    fn read_from<R: ByteReader>(source: &mut R) -> Result<Self, DeserializationError> {
        // read values
        let num_value_bytes = source.read_u32()?;
        let values = source.read_vec(num_value_bytes as usize)?;

        // read paths
        let num_paths_bytes = source.read_u32()?;
        let paths = source.read_vec(num_paths_bytes as usize)?;

        Ok(Queries { paths, values })
    }
}
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct JointTraceQueries {
    paths: Vec<u8>,
    values: Vec<u8>,
    value_vec: Vec<Vec<u8>>,
}

impl JointTraceQueries {
    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    /// Returns queries constructed from evaluations of a set of functions at some number of points
    /// in a domain and their corresponding Merkle authentication paths.
    ///
    /// For each evaluation point, the same number of values must be provided, and a hash of
    /// these values must be equal to a leaf node in the corresponding Merkle authentication path.
    ///
    /// # Panics
    /// Panics if:
    /// * No queries were provided (`query_values` is an empty vector).
    /// * Any of the queries does not contain any evaluations.
    /// * Not all queries contain the same number of evaluations.
    pub fn new<H: Hasher, E: FieldElement>(
        merkle_proof: BatchMerkleProof<H>,
        query_values: Vec<Vec<E>>,
        query_value_vec: Vec<Vec<Vec<E>>>,
    ) -> Self {
        assert!(!query_values.is_empty(), "query values cannot be empty");
        let elements_per_query = query_values[0].len();
        assert_ne!(
            elements_per_query, 0,
            "a query must contain at least one evaluation"
        );
        let mut vecs_per_query_value = Vec::new();
        for query_value in query_value_vec.iter() {
            assert!(!query_value.is_empty(), "query values cannot be empty");
            let elements_per_query_value = query_value[0].len();
            assert_ne!(
                elements_per_query_value, 0,
                "a query must contain at least one evaluation"
            );
            vecs_per_query_value.push(elements_per_query_value);
        }
        // TODO: add debug check that values actually hash into the leaf nodes of the batch proof

        // concatenate all elements together into a single vector of bytes
        let num_queries = query_values.len();
        let mut values = Vec::with_capacity(num_queries * elements_per_query * E::ELEMENT_BYTES);
        for elements in query_values.iter() {
            assert_eq!(
                elements.len(),
                elements_per_query,
                "all queries must contain the same number of evaluations"
            );
            values.write(elements);
        }
        let mut value_vec = Vec::new();
        for (i, query_value) in query_value_vec.iter().enumerate() {
            let mut value =
                Vec::with_capacity(num_queries * vecs_per_query_value[i] * E::ELEMENT_BYTES);
            for elements in query_value.iter() {
                assert_eq!(
                    elements.len(),
                    vecs_per_query_value[i],
                    "all queries must contain the same number of evaluations"
                );
                value.write(elements);
            }
            value_vec.push(value);
        }
        // serialize internal nodes of the batch Merkle proof; we care about internal nodes only
        // because leaf nodes can be reconstructed from hashes of query values
        let paths = merkle_proof.serialize_nodes();

        JointTraceQueries {
            paths,
            values,
            value_vec,
        }
    }

    // PARSER
    // --------------------------------------------------------------------------------------------
    /// Convert internally stored bytes into a set of query values and the corresponding Merkle
    /// authentication paths.
    ///
    /// # Panics
    /// Panics if:
    /// * `domain_size` is not a power of two.
    /// * `num_queries` is zero.
    /// * `values_per_query` is zero.
    pub fn parse<H, E>(
        self,
        domain_size: usize,
        num_queries: usize,
        values_per_query_vec: Vec<usize>,
    ) -> Result<(BatchMerkleProof<H>, Table<E>, Vec<Table<E>>), DeserializationError>
    where
        E: FieldElement,
        H: ElementHasher<BaseField = E::BaseField>,
    {
        assert!(
            domain_size.is_power_of_two(),
            "domain size must be a power of two"
        );
        assert!(num_queries > 0, "there must be at least one query");
        let mut values_of_all_queries: usize = 0;
        for values_per_query in values_per_query_vec.iter() {
            assert!(
                *values_per_query > 0,
                "a query must contain at least one value"
            );
            values_of_all_queries += values_per_query;
        }

        // make sure we have enough bytes to read the expected number of queries
        let num_query_bytes = E::ELEMENT_BYTES * (values_of_all_queries);
        // !!!
        // Bytes expected are double because leaf is double in size now
        let expected_bytes = num_queries * num_query_bytes;
        if self.values.len() != expected_bytes {
            return Err(DeserializationError::InvalidValue(format!(
                "expected {} query value bytes, but was {}",
                expected_bytes,
                self.values.len()
            )));
        }

        // read bytes corresponding to each query, convert them into field elements,
        // and also hash them to build leaf nodes of the batch Merkle proof
        let query_values =
            Table::<E>::from_bytes(&self.values, num_queries, values_of_all_queries)?;
        let mut query_value_vec = Vec::new();
        for (value, values_per_query) in self.value_vec.iter().zip(values_per_query_vec.iter()) {
            let query_value = Table::<E>::from_bytes(&value, num_queries, *values_per_query)?;
            query_value_vec.push(query_value);
        }
        //let query_value = Table::<E>::from_bytes(&self.value, num_queries, values_per_query)?;
        let hashed_queries = query_values
            .rows()
            .map(|row| H::hash_elements(row))
            .collect();

        // build batch Merkle proof
        let mut reader = SliceReader::new(&self.paths);
        let tree_depth = domain_size.ilog2() as u8;
        let merkle_proof = BatchMerkleProof::deserialize(&mut reader, hashed_queries, tree_depth)?;
        if reader.has_more_bytes() {
            return Err(DeserializationError::UnconsumedBytes);
        }

        Ok((merkle_proof, query_values, query_value_vec))
    }
}

impl Serializable for JointTraceQueries {
    /// Serializes `self` and writes the resulting bytes into the `target`.
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        // write value bytes
        target.write_u32(self.values.len() as u32);
        target.write_bytes(&self.values);

        // write path bytes
        target.write_u32(self.paths.len() as u32);
        target.write_bytes(&self.paths);
    }
}

impl Deserializable for JointTraceQueries {
    /// Reads a query struct from the specified `source` and returns the result
    ///
    /// # Errors
    /// Returns an error of a valid query struct could not be read from the specified source.
    fn read_from<R: ByteReader>(source: &mut R) -> Result<Self, DeserializationError> {
        // read values
        let num_value_bytes = source.read_u32()?;
        let values = source.read_vec(num_value_bytes as usize)?;

        // read paths
        let num_paths_bytes = source.read_u32()?;
        let paths = source.read_vec(num_paths_bytes as usize)?;

        Ok(JointTraceQueries {
            paths,
            values,
            value_vec: vec![vec![]],
        })
    }
}
