//! Vivaldi coordinate system implementation
//!
//! ```mermaid
//! graph TB
//!    subgraph "Vivaldi Coordinate System"
//!        Actor1[Actor A] --> Vec1[Vector Components]
//!        Actor1 --> H1[Height]
//!        Actor1 --> Adj1[Adjustment]
//!
//!        Actor2[Actor B] --> Vec2[Vector Components]
//!        Actor2 --> H2[Height]
//!        Actor2 --> Adj2[Adjustment]
//!
//!        Vec1 & Vec2 --> ED[Euclidean Distance]
//!        H1 & H2 --> HD[Height Distance]
//!        Adj1 & Adj2 --> ADJ[Adjustment Factor]
//!
//!        ED & HD & ADJ --> TD[Total Distance]
//!    end
//!
//!    classDef component fill:#f9f,stroke:#333
//!    classDef calculation fill:#bbf,stroke:#333
//!
//!    class Vec1,Vec2,H1,H2,Adj1,Adj2 component
//!    class ED,HD,ADJ,TD calculation
//!
#[cfg(feature = "service")]
use jetstream::prelude::*;
use std::time::Duration;

// rand 0.10 moved `random`/`random_range` off `Rng` and onto `RngExt`, which
// is blanket-implemented for every `Rng`. The `impl rand::Rng` bounds below
// stay as they are; only the trait has to be in scope.
use rand::RngExt as _;

/// A Vivaldi coordinate
#[derive(Debug, Clone, JetStreamWireFormat)]
pub struct Coordinate {
    /// Euclidean portion of the coordinate (in seconds)
    pub(crate) vec: Vec<f64>,
    /// Confidence in the coordinate (dimensionless)
    pub(crate) error: f64,
    /// Distance offset based on observations (in seconds)
    pub(crate) adjustment: f64,
    /// Distance offset for non-Euclidean effects (in seconds)
    pub(crate) height: f64,
}

/// Errors that can occur when working with coordinates
#[derive(Debug)]
pub enum CoordinateError {
    /// The coordinate dimensionality does not match
    DimensionalityConflict,
    /// The coordinate contains invalid values
    InvalidValues,
    /// The round trip time is not in a valid range
    InvalidRtt,
    /// The configured dimensionality is zero
    InvalidDimensionality,
}

impl std::fmt::Display for CoordinateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            CoordinateError::DimensionalityConflict => "coordinate dimensionality does not match",
            CoordinateError::InvalidValues => "coordinate contains invalid values",
            CoordinateError::InvalidRtt => "round trip time not in valid range",
            CoordinateError::InvalidDimensionality => "coordinate dimensionality is zero",
        })
    }
}

impl std::error::Error for CoordinateError {}

// Constants
pub(crate) const SECONDS_TO_NANOSECONDS: f64 = 1.0e9;

pub(crate) const ZERO_THRESHOLD: f64 = 1.0e-6;

/// Configuration for the Vivaldi coordinate system
///
/// Pure configuration: it holds no random number generator, so it stays
/// wire-encodable and comparable. Randomness is needed in exactly one
/// place -- picking an arbitrary direction when two coordinates sit on top
/// of each other -- so it is passed to [`Coordinate::apply_force`] instead
/// of being carried here.
#[derive(Debug, Clone, PartialEq, JetStreamWireFormat)]
pub struct Config {
    /// The dimensionality of the coordinate system
    pub dimensionality: usize,
    /// Maximum error value and default for new coordinates
    pub vivaldi_error_max: f64,
    /// Controls maximum impact of observations on confidence
    pub vivaldi_ce: f64,
    /// Controls maximum impact of observations on coordinates
    pub vivaldi_cc: f64,
    /// Number of samples for adjustment window (0 disables feature)
    pub adjustment_window_size: usize,
    /// Minimum height value (must be positive)
    pub height_min: f64,
    /// Maximum samples retained per actor for latency filtering
    pub latency_filter_size: usize,
    /// Tuning factor for gravity effect
    pub gravity_rho: f64,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            dimensionality: 8,
            vivaldi_error_max: 1.5,
            vivaldi_ce: 0.25,
            vivaldi_cc: 0.25,
            adjustment_window_size: 20,
            height_min: 10.0e-6,
            latency_filter_size: 3,
            gravity_rho: 150.0,
        }
    }
}

impl Coordinate {
    /// Creates a coordinate at the origin.
    ///
    /// A new node starts with no information about where it sits, so its
    /// vector is all zeros and its error is the configured maximum -- the
    /// least confident value there is, which lets the first observations
    /// move it furthest.
    ///
    /// [`CoordinateError::InvalidDimensionality`] if the configured
    /// dimensionality is zero: a coordinate with no components has no
    /// direction to push along, so [`Coordinate::apply_force`] could not
    /// separate two of them.
    pub fn new(config: &Config) -> std::result::Result<Self, CoordinateError> {
        if config.dimensionality == 0 {
            return Err(CoordinateError::InvalidDimensionality);
        }
        Ok(Coordinate {
            vec: vec![0.0; config.dimensionality],
            error: config.vivaldi_error_max,
            adjustment: 0.0,
            height: config.height_min,
        })
    }

    /// Checks if all components of the coordinate are valid
    pub fn is_valid(&self) -> bool {
        self.vec.iter().all(|&x| Self::component_is_valid(x))
            && Self::component_is_valid(self.error)
            && Self::component_is_valid(self.adjustment)
            && Self::component_is_valid(self.height)
    }

    pub(crate) fn component_is_valid(f: f64) -> bool {
        !f.is_infinite() && !f.is_nan()
    }

    /// Checks dimensional compatibility with another coordinate
    pub fn is_compatible_with(&self, other: &Coordinate) -> bool {
        self.vec.len() == other.vec.len()
    }

    /// Returns the distance between this coordinate and another
    pub fn distance_to(
        &self,
        other: &Coordinate,
    ) -> std::result::Result<Duration, CoordinateError> {
        if !self.is_compatible_with(other) {
            return Err(CoordinateError::DimensionalityConflict);
        }

        let dist = self.raw_distance_to(other);
        let adjusted_dist = dist + self.adjustment + other.adjustment;
        let final_dist = if adjusted_dist > 0.0 {
            adjusted_dist
        } else {
            dist
        };

        Ok(Duration::from_nanos(
            (final_dist * SECONDS_TO_NANOSECONDS) as u64,
        ))
    }

    /// Calculates raw Vivaldi distance without adjustments
    pub(crate) fn raw_distance_to(&self, other: &Coordinate) -> f64 {
        let euclidean_dist = self
            .vec
            .iter()
            .zip(other.vec.iter())
            .map(|(&a, &b)| (a - b).powi(2))
            .sum::<f64>()
            .sqrt();

        euclidean_dist + self.height + other.height
    }

    /// Applies force from another coordinate's direction
    ///
    /// `rng` is only consulted when the two coordinates are close enough
    /// to be indistinguishable, where the direction to push is arbitrary
    /// and has to come from somewhere. Passing it in keeps that branch
    /// reproducible under test.
    pub fn apply_force(
        &self,
        config: &Config,
        force: f64,
        other: &Coordinate,
        rng: &mut impl rand::Rng,
    ) -> std::result::Result<Coordinate, CoordinateError> {
        if !self.is_compatible_with(other) {
            return Err(CoordinateError::DimensionalityConflict);
        }

        let (unit, mag) = self.unit_vector_at(other, rng);
        let mut new_coord = self.clone();

        // Update vector components
        (0..self.vec.len()).for_each(|i| {
            new_coord.vec[i] += unit[i] * force;
        });

        // Update height if points aren't too close
        if mag > ZERO_THRESHOLD {
            new_coord.height = (new_coord.height + other.height) * force / mag + new_coord.height;
            new_coord.height = new_coord.height.max(config.height_min);
        }

        Ok(new_coord)
    }

    /// Calculates unit vector pointing from this coordinate to another
    ///
    /// Returns the direction and the original magnitude. A magnitude of
    /// zero means the two coordinates were too close to separate and the
    /// direction is arbitrary rather than measured, which the caller must
    /// not mistake for "no distance".
    pub(crate) fn unit_vector_at(
        &self,
        other: &Coordinate,
        rng: &mut impl rand::Rng,
    ) -> (Vec<f64>, f64) {
        let mut diff: Vec<f64> = self
            .vec
            .iter()
            .zip(other.vec.iter())
            .map(|(&a, &b)| a - b)
            .collect();

        let mag = (diff.iter().map(|&x| x * x).sum::<f64>()).sqrt();

        // If points aren't too close, normalize the vector
        if mag > ZERO_THRESHOLD {
            for d in diff.iter_mut() {
                *d /= mag;
            }
            return (diff, mag);
        }

        // Generate random unit vector if points are too close.
        // Not cryptographic: any direction will do, it only has to be
        // arbitrary so two coincident nodes don't push each other the same
        // way forever.
        diff = diff.iter().map(|_| rng.random::<f64>() - 0.5).collect();
        let mag = (diff.iter().map(|&x| x * x).sum::<f64>()).sqrt();

        if mag > ZERO_THRESHOLD {
            for d in diff.iter_mut() {
                *d /= mag;
            }
            return (diff, 0.0);
        }

        // Last resort: unit vector along first dimension
        let mut unit = vec![0.0; self.vec.len()];
        unit[0] = 1.0;
        (unit, 0.0)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::HashMap;

    use rand::RngExt as _;
    use rand::SeedableRng as _;
    use rand::seq::IndexedRandom as _;

    use super::*;

    fn _verify_equal_vectors(v1: &[f64], v2: &[f64], epsilon: f64) {
        assert_eq!(v1.len(), v2.len());
        for (a, b) in v1.iter().zip(v2.iter()) {
            assert!((a - b).abs() < epsilon, "Expected {a} to equal {b}");
        }
    }

    #[test]
    fn test_new_coordinate() {
        let config = Config::default();
        let coord = Coordinate::new(&config).unwrap();
        assert_eq!(coord.vec.len(), config.dimensionality);
        assert_eq!(coord.error, config.vivaldi_error_max);
        assert_eq!(coord.height, config.height_min);
    }

    /// A zero-dimensional configuration is refused at construction. Accepted, its
    /// coordinates reached `apply_force`'s last resort with an empty vector and
    /// panicked indexing `unit[0]`.
    #[test]
    fn a_zero_dimensional_config_is_refused() {
        let config = Config {
            dimensionality: 0,
            ..Config::default()
        };
        assert!(matches!(
            Coordinate::new(&config),
            Err(CoordinateError::InvalidDimensionality)
        ));
    }

    #[test]
    fn test_is_valid() {
        let config = Config::default();
        let mut coord = Coordinate::new(&config).unwrap();
        assert!(coord.is_valid());

        coord.vec[0] = f64::NAN;
        assert!(!coord.is_valid());

        coord.vec[0] = f64::INFINITY;
        assert!(!coord.is_valid());
    }

    #[test]
    fn test_incompatible_dimensions() {
        let mut config = Config {
            dimensionality: 3,
            ..Default::default()
        };

        let coord1 = Coordinate::new(&config).unwrap();

        config.dimensionality = 2;
        let coord2 = Coordinate::new(&config).unwrap();

        assert!(!coord1.is_compatible_with(&coord2));
        assert!(coord1.distance_to(&coord2).is_err());
    }
    #[test]
    fn test_distance_calculation() {
        let config = Config::default();
        let mut coord1 = Coordinate::new(&config).unwrap();
        let mut coord2 = Coordinate::new(&config).unwrap();

        // Set first 3 dimensions and pad rest with zeros
        coord1.vec = vec![-0.5, 1.3, 2.4];
        coord2.vec = vec![1.2, -2.3, 3.4];

        while coord1.vec.len() < config.dimensionality {
            coord1.vec.push(0.0);
            coord2.vec.push(0.0);
        }

        // Calculate euclidean distance
        let euclidean_distance = 4.104875150354758;

        // Expected total distance includes heights
        let expected_distance = euclidean_distance + coord1.height + coord2.height;

        let dist = coord1.distance_to(&coord2).unwrap();
        let got = dist.as_secs_f64();
        let diff = (got - expected_distance).abs();

        println!("Distance calculation:");
        println!("Got:      {}", got);
        println!("Expected: {}", expected_distance);
        println!("Diff:     {}", diff);

        assert!(
            diff < 1e-6,
            "Distance calculation failed:\nGot {}\nWanted {}\nDiff {}",
            got,
            expected_distance,
            diff
        );

        // Additional verification tests
        let mut height_free_coord1 = coord1.clone();
        let mut height_free_coord2 = coord2.clone();

        // Test with zero heights
        height_free_coord1.height = 0.0;
        height_free_coord2.height = 0.0;

        let pure_euclidean = height_free_coord1.distance_to(&height_free_coord2).unwrap();
        assert!(
            (pure_euclidean.as_secs_f64() - euclidean_distance).abs() < 1e-6,
            "Pure Euclidean distance failed:\nGot {}\nWanted {}",
            pure_euclidean.as_secs_f64(),
            euclidean_distance
        );
    }

    // Add test for pure height calculation
    #[test]
    fn test_height_contribution() {
        let config = Config::default();
        let coord1 = Coordinate::new(&config).unwrap();
        let coord2 = Coordinate::new(&config).unwrap();

        // With default config, both coords should have height_min
        let expected_height_contribution = config.height_min * 2.0;
        let dist = coord1.distance_to(&coord2).unwrap();

        assert!(
            (dist.as_secs_f64() - expected_height_contribution).abs() < 1e-6,
            "Height-only distance failed:\nGot {}\nWanted {}",
            dist.as_secs_f64(),
            expected_height_contribution
        );
    }

    // Add test for adjustment contribution
    #[test]
    fn test_adjustment_contribution() {
        let config = Config::default();
        let mut coord1 = Coordinate::new(&config).unwrap();
        let mut coord2 = Coordinate::new(&config).unwrap();

        coord1.adjustment = 0.1;
        coord2.adjustment = 0.2;

        let base_dist = coord1.height + coord2.height; // Just heights, vectors are 0
        let expected_dist = base_dist + 0.3; // 0.3 is sum of adjustments

        let dist = coord1.distance_to(&coord2).unwrap();

        assert!(
            (dist.as_secs_f64() - expected_dist).abs() < 1e-6,
            "Adjustment distance failed:\nGot {}\nWanted {}",
            dist.as_secs_f64(),
            expected_dist
        );
    }

    // Push 20 actors around against each other and check the system stays
    // well-formed: every coordinate finite, the right dimensionality, and
    // height never pushed below the configured floor.
    #[test]
    fn test_map_generation() {
        let config = Config::default();
        let mut coordinates = vec![Coordinate::new(&config).unwrap(); 20];
        let mut actor_map: HashMap<String, Coordinate> = HashMap::new();

        // Seeded, so a failure here reproduces rather than appearing once
        // in a hundred runs.
        let mut rng = rand::rngs::StdRng::seed_from_u64(2);

        // Apply force to each coordinate in relation to another random one.
        // `other` is cloned because the push both reads a coordinate from
        // the vector and writes one back into it.
        for i in 0..coordinates.len() {
            let other = coordinates.choose(&mut rng).unwrap().clone();
            let force: f64 = rng.random_range(0.0..2.0);
            coordinates[i] = coordinates[i]
                .apply_force(&config, force, &other, &mut rng)
                .unwrap();

            actor_map.insert(format!("actor_{i}"), coordinates[i].clone());
        }

        assert_eq!(actor_map.len(), coordinates.len());
        for (name, coord) in &actor_map {
            assert!(coord.is_valid(), "{name} went non-finite");
            assert_eq!(
                coord.vec.len(),
                config.dimensionality,
                "{name} changed rank"
            );
            assert!(
                coord.height >= config.height_min,
                "{name} fell below the height floor: {} < {}",
                coord.height,
                config.height_min
            );
        }
    }
}
