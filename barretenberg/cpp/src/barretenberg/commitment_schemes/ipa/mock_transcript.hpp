#include "barretenberg/ecc/curves/grumpkin/grumpkin.hpp"
#include "barretenberg/numeric/uint256/uint256.hpp"
#include <vector>
namespace bb {
/**
 * @brief Mock transcript class used by IPA tests and fuzzer
 *
 * @details This transcript can send previously determined challenges instead of ones generated by Fiat Shamir. It can
 * also store elements received from the prover
 *
 */
class MockTranscript {
  public:
    // Vector of challenges sent to the verifier
    std::vector<uint256_t> challenges;
    // Vector of group elements received from the prover / sent to the verifier
    std::vector<bb::curve::Grumpkin::AffineElement> group_elements;
    // Vector of field elements received from the prover / sent to the verifier. uint256_t is used to ignore field type
    std::vector<uint256_t> field_elements;

    // Indices of the elements being sampled
    size_t current_challenge_index = 0;
    size_t current_field_index = 0;
    size_t current_group_index = 0;

    /**
     * @brief Initialize the transcript (requires to submit the challenges)
     *
     * @param challenges_ Challenges that will be sent to the prover/verifier
     * @param group_elements_ Group elements sent to the verifier
     * @param field_elements_ Field elements sent to the verifier
     */
    void initialize(std::vector<uint256_t> challenges_,
                    std::vector<bb::curve::Grumpkin::AffineElement> group_elements_ = {},
                    std::vector<uint256_t> field_elements_ = {})
    {
        challenges = std::move(challenges_);
        current_challenge_index = 0;
        current_field_index = 0;
        current_group_index = 0;
        group_elements = std::move(group_elements_);
        field_elements = std::move(field_elements_);
    }
    /**
     * @brief Reset the indices of elements sampled after using the transcript with the prover
     *
     * @details After the transcipt received elements from the prover, this method allows to reset counters so that the
     * verifier can receive those elements
     */
    void reset_indices()
    {
        current_challenge_index = 0;
        current_field_index = 0;
        current_challenge_index = 0;
    }
    /**
     * @brief Send something that can be converted to uint256_t to the verifier (used for field elements)
     *
     */
    template <typename T> void send_to_verifier(const std::string&, const T& element)
    {
        // GCC breaks explicit specialization, so I have to do this
        if constexpr (std::is_same_v<bb::curve::Grumpkin::AffineElement, T>) {

            group_elements.push_back(element);
        } else {
            field_elements.push_back(static_cast<uint256_t>(element));
        }
    }

    /**
     * @brief Get a challenge from the verifier
     *
     */
    template <typename T> T get_challenge(const std::string&)
    {
        // No heap overreads, please
        ASSERT(current_challenge_index < challenges.size());
        T result = static_cast<T>(challenges[current_challenge_index]);
        current_challenge_index++;
        return result;
    }
    /**
     * @brief Receive elements from the prover
     *
     */
    template <typename T> T receive_from_prover(const std::string&)
    {
        if constexpr (std::is_same_v<bb::curve::Grumpkin::ScalarField, T> ||
                      std::is_same_v<bb::curve::Grumpkin::BaseField, T>) {
            ASSERT(field_elements.size() > current_field_index);
            return field_elements[current_field_index++];
        }
        if constexpr (std::is_same_v<bb::curve::Grumpkin::AffineElement, T>) {
            ASSERT(group_elements.size() > current_group_index);
            return group_elements[current_group_index++];
        }
    }
};
} // namespace bb