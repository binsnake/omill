#pragma region Header Guard

#ifndef MUT_HXX
#define MUT_HXX

#pragma endregion

#pragma region Imports

// ========================= Imports =========================
// Standard library imports for bit manipulation, random number generation, type traits, integer types, and time
#include <bit>
#include <random>
#include <type_traits>
#include <mutex>
#include <atomic>
#include <thread>
#include <cstdint>
#include <ctime>

// Extended imports for compiler intrinsics and SIMD operations
#include <intrin.h>
#include <immintrin.h>

#pragma endregion

#pragma region Optimizations

#ifdef NDEBUG
// Disable runtime checks and stack protection, enable optimizations for release builds
#pragma runtime_checks("scu", off)
#pragma strict_gs_check(off)
#pragma optimize("s", on)
#pragma __forceinline_depth(255)
#pragma __forceinline_recursion(on)
#endif

#pragma endregion

#pragma region Macros

#define MAKERD32()std::random_device ___RD___;																	\
std::mt19937 r(std::time(nullptr) ^ ___RD___() ^ (std::hash<std::thread::id>{}(std::this_thread::get_id())));

#define MAKERD64()std::random_device ___RD___;																	\
std::mt19937_64 r(std::time(nullptr) ^ ___RD___() ^ (std::hash<std::thread::id>{}(std::this_thread::get_id())));

// ========================= Macros =========================
#ifdef _MSC_VER
// Bitwise rotate left and right macros for different integer sizes (MSVC intrinsics)
#define rshl(BASE, MODIFIER) ((sizeof(decltype(BASE)) == sizeof(std::uint8_t)) ? (_rotl8(BASE, (std::uint8_t)MODIFIER)) : (sizeof(decltype(BASE)) == sizeof(std::uint16_t)) ? (_rotl16(BASE, (std::uint8_t)MODIFIER)) : (sizeof(decltype(BASE)) == sizeof(std::uint32_t)) ? (_rotl(BASE, (std::int32_t)MODIFIER)) :  (sizeof(decltype(BASE)) == sizeof(std::uint64_t)) ? (_rotl64(BASE, (std::int32_t)MODIFIER)) : NULL)
#define rshr(BASE, MODIFIER) ((sizeof(decltype(BASE)) == sizeof(std::uint8_t)) ? (_rotr8(BASE, (std::uint8_t)MODIFIER)) : (sizeof(decltype(BASE)) == sizeof(std::uint16_t)) ? (_rotr16(BASE, (std::uint8_t)MODIFIER)) : (sizeof(decltype(BASE)) == sizeof(std::uint32_t)) ? (_rotr(BASE, (std::int32_t)MODIFIER)) :  (sizeof(decltype(BASE)) == sizeof(std::uint64_t)) ? (_rotr64(BASE, (std::int32_t)MODIFIER)) : NULL)
#else
// Portable C++20 constexpr rotate left/right for non-MSVC compilers
// Ensures only non-boolean integral types are accepted
// Uses std::rotl and std::rotr for bitwise rotation
template <typename T>
[[nodiscard]] constexpr auto rshl(T base, const std::int32_t modifier) noexcept {

	static_assert(std::is_integral_v<T> && !std::is_same_v<std::remove_cv_t<T>, bool>,
		"rshl() Requires a non-Boolean Integral Type.");

	using u_T = std::make_unsigned_t<T>;
	return std::rotl(static_cast<u_T>(base), modifier);
}

template <typename T>
[[nodiscard]] constexpr auto rshr(T base, const std::int32_t modifier) noexcept {

	static_assert(std::is_integral_v<T> && !std::is_same_v<std::remove_cv_t<T>, bool>,
		"rshr() Requires a non-Boolean Integral Type.");

	using u_T = std::make_unsigned_t<T>;
	return std::rotr(static_cast<u_T>(base), modifier);
}
#endif

#pragma endregion

#pragma region Type Definitions

// ==========================================================

// ========================= Type Definitions =========================
// Enumeration for supported mutation types (integer and floating point)
typedef enum mut_t : std::uint8_t {

	i8 = 0,
	ui8 = 1,

	i16 = 2,
	ui16 = 3,

	i32 = 4,
	ui32 = 5,

	i64 = 6,
	ui64 = 7,

	f32 = 8,
	f64 = 9,

	err_t = 12
};

#pragma endregion

#pragma region Evaluation Functions

// Returns the mut_t enum value for a given type T
// Used to identify the base type for mutation logic
template<typename T>
static __forceinline constexpr const mut_t get_mut_t(const T object) noexcept {

	using base_t = std::remove_cv_t<T>;

	if		constexpr (std::is_same_v<base_t, std::int8_t>)
		return i8;
	else if constexpr (std::is_same_v<base_t, std::uint8_t>)
		return ui8;
	else if constexpr (std::is_same_v<base_t, std::int16_t>)
		return i16;
	else if constexpr (std::is_same_v<base_t, std::uint16_t>)
		return ui16;
	else if constexpr (std::is_same_v<base_t, std::int32_t>)
		return i32;
	else if constexpr (std::is_same_v<base_t, std::uint32_t>)
		return ui32;
	else if constexpr (std::is_same_v<base_t, std::int64_t>)
		return i64;
	else if constexpr (std::is_same_v<base_t, std::uint64_t>)
		return ui64;
	else if constexpr (std::is_same_v<base_t, float>)
		return f32;
	else if constexpr (std::is_same_v<base_t, double> || std::is_same_v<base_t, long double>)
		return f64;
	else if constexpr (std::is_same_v<base_t, bool>)
		return ui8;
	else if constexpr (std::is_same_v<base_t, long>)
		return (sizeof(long) == sizeof(std::int32_t) ? i32 : i64);
	else if constexpr (std::is_same_v<base_t, unsigned long>)
		return (sizeof(unsigned long) == sizeof(std::uint32_t) ? ui32 : ui64);
	else if constexpr (std::is_pointer_v<base_t>) {
#ifdef _M_X64
		return ui64;
#else
		return ui32;
#endif
	}

	return err_t;
}

// Returns the position of the most significant set bit in the object
// Used for bit manipulation and mutation logic
template<typename T>
static __forceinline const std::uint8_t __fastcall max_headroom_t(const T object) noexcept {

	std::uint8_t r_position = 0;
	for (std::size_t i = 0; i < sizeof(T) * 8; ++i)
		if (object & (T(0x1) << i))
			r_position = i;

	return r_position;
}

#pragma endregion

// ========================= cmut Class =========================
// cmut<T> is a template class for storing and mutating values of type T
// It provides obfuscation, mutation, and secure memory handling for primitive types
// The class supports both integer and floating point types, and uses SIMD for some operations
template<typename T>
class cmut {

private:

#pragma region Global Variables

	// ----------- Base Globals -----------
	// base_type: Stores the mut_t enum for the type T
	// seed: Random seed for mutation logic
	// cmut_mtx: Mutex to Prevent Race-Conditions in R/W-Access
	mut_t									base_type;

	std::uint32_t							seed = std::mt19937(std::time(nullptr))();

	/*
		§12.6.2/8 [class.base.init]
		C++17 Standard Draft N4659
		(Section 12.6.2: Initializing bases and members, paragraph 8)
		"A mem-initializer is evaluated as part of the initialization of the object. In particular, it is evaluated before the body of the constructor is entered (12.6.2/5). If a constructor’s parameter expression or a mem-initializer uses this, it designates a partially-constructed object..."
		"...Any operations on such an object other than calling its non-virtual member functions, accessing its non-static data members, or performing class member access that uses the . or -> operators are undefined behavior unless the object’s lifetime has begun (6.7.3)."

		The CXX Standard Allows for, infact Implements and even Promotes something which shouldn't exist - The Ability for a Move / Copy Ctor to Interrupt the Execution of the Base Ctor,
		Likewise Writing code in the Move / Copy Ctor, that DEPENDS on the Base Ctor's FULL EXECUTION, can and will Fail without Proper Guards / Fixes.
		This means you have to Write Code that May NOT Expect for the Object Instance to be Initialized, to any Degree ;

		In our case Specifically, it Means that the Mutex we Locked out of Necessity in the cmut Ctor, shall still be Locked by the Ctor, when Executing an Entirely Different Method which is REQUIRED to be
		Thread-Safe and likewise Requires a Mutex Guard.
	*/
	mutable std::recursive_mutex			cmut_mtx;

	volatile bool							is_ctor_lock = false;

	// ----------- Binary Mutation Trackers -----------
	// Track how many bits were shifted for each mutated form
		// How many bits were Shifted Left per each Mutated Form
	std::uint8_t							m_sh_16;
	std::uint8_t							m_sh_32;
	std::uint8_t							m_sh_64;
	std::uint8_t							m_sh_v128;
	std::uint8_t							m_sh_v128_64;

	// ----------- Mutated / Polymorphic Storage -----------
	// Storage for mutated forms of the value, including split words and SIMD vectors
	// original_set_map: Bit map of the original value
		// Bits are Stored in Reverse-Order Low-High
	bool									original_set_map[128]{ false };

	std::uint16_t							m_ui16;

	std::uint8_t							m_rsh_ui32;
	std::uint32_t							m_ui32;

	alignas(0x2) std::uint16_t				m_ui64_split16[4];
	alignas(0x4) std::uint32_t				m_ui64_split32[2];

	// m_v128 is used to Mutate Lower Primitive Types
	__m128i									m_v128;

	// Fallback to Bitmap for 64-bit or Circular-Rotate 2 32-bit Integers, m_rsh_ui64 Descripts amount of Bits Circularly Rotated per-Subword split Word (both Subword 32/16)
	std::uint8_t							m_rsh_ui64;
	std::uint64_t							m_ui64;

	// ----------- Control Flow Flags / Modulators -----------
	// Flags and modes that control how mutation and reconstruction are performed
	// reconstruct_mode: Determines which reconstruction method to use
	// rec_ui8_mode, rec_ui16_mode, rec_ui32_mode, rec_ui64_mode: Selects sub-modes for each type
		/*
			0 = SideWord / SubWord Mutation Reconstruction
			1 = Mapping Reconstruction
		*/
	bool									reconstruct_mode = static_cast<bool>(seed % 2);

	std::uint8_t							rec_ui8_mode = seed % 4;
	std::uint8_t							rec_ui16_mode = seed % 3;
	std::uint8_t							rec_ui32_mode = seed % 2;
	std::uint8_t							rec_ui64_mode = rec_ui16_mode;

#pragma endregion

#pragma region Core Type Mutations / Reconstruction

	// ----------- Type Deconstruction / Mutation(s) -----------
	// deconstruct_t: Mutates the input value into various forms for obfuscation
	// Uses random shifts, splits, and SIMD packing
	template<typename _T>
	__forceinline void deconstruct_t(volatile _T object, std::mt19937& r) noexcept {

		const std::size_t	headroom = max_headroom_t(object);

		const std::size_t	max_pos_ui16 = (sizeof(std::uint16_t) * 8) - 1 - headroom;
		const std::size_t	max_pos_ui32 = (sizeof(std::uint32_t) * 8) - 1 - headroom;
		const std::size_t	max_pos_ui64 = (sizeof(std::uint64_t) * 8) - 1 - headroom;

		m_sh_16 = r() % (max_pos_ui16 + 1);
		m_sh_32 = r() % (max_pos_ui32 + 1);
		m_sh_64 = r() % (max_pos_ui64 + 1);
		m_sh_v128 = r() % (sizeof(__m128i) / sizeof(std::uint32_t));

		std::uint8_t		dummy_bytect16 = m_sh_16 / 8;
		std::uint8_t		dummy_bytect32 = m_sh_32 / 8;
		std::uint8_t		dummy_bytect64 = m_sh_64 / 8;

		// Fill Unused Bytes with Randomized Data
		for (std::size_t i = 0; i < dummy_bytect16; ++i)
			m_ui16 |= static_cast<std::uint16_t>(static_cast<std::uint8_t>(r() & 0xFF)) << (i * 8);

		for (std::size_t i = 0; i < dummy_bytect32; ++i)
			m_ui16 |= static_cast<std::uint32_t>(static_cast<std::uint8_t>(r() & 0xFF)) << (i * 8);

		for (std::size_t i = 0; i < dummy_bytect64; ++i)
			m_ui16 |= static_cast<std::uint64_t>(static_cast<std::uint8_t>(r() & 0xFF)) << (i * 8);

		switch (base_type) {

		case i8:
		case ui8: {

			m_ui16 = static_cast<std::uint16_t>(object) << m_sh_16;
			m_ui32 = static_cast<std::uint32_t>(object) << m_sh_32;
			m_ui64 = static_cast<std::uint64_t>(object) << m_sh_64;

			m_v128 = _mm_set_epi32(

				m_sh_v128 == 3 ? static_cast<std::uint32_t>(object) << m_sh_32 : r(),
				m_sh_v128 == 2 ? static_cast<std::uint32_t>(object) << m_sh_32 : r(),
				m_sh_v128 == 1 ? static_cast<std::uint32_t>(object) << m_sh_32 : r(),
				m_sh_v128 == 0 ? static_cast<std::uint32_t>(object) << m_sh_32 : r()
			);

			break;
		}
		case i16:
		case ui16: {

			m_ui32 = static_cast<std::uint32_t>(object) << m_sh_32;
			m_ui64 = static_cast<std::uint64_t>(object) << m_sh_64;

			m_v128 = _mm_set_epi32(

				m_sh_v128 == 3 ? static_cast<std::uint32_t>(object) << m_sh_32 : r(),
				m_sh_v128 == 2 ? static_cast<std::uint32_t>(object) << m_sh_32 : r(),
				m_sh_v128 == 1 ? static_cast<std::uint32_t>(object) << m_sh_32 : r(),
				m_sh_v128 == 0 ? static_cast<std::uint32_t>(object) << m_sh_32 : r()
			);

			break;
		}
		case f32:
		case i32:
		case ui32: {

			m_rsh_ui32 = r();
			m_ui64 = static_cast<std::uint64_t>(object) << m_sh_64;

			m_v128 = _mm_set_epi32(

				m_sh_v128 == 3 ? rshl(object, m_rsh_ui32) : r(),
				m_sh_v128 == 2 ? rshl(object, m_rsh_ui32) : r(),
				m_sh_v128 == 1 ? rshl(object, m_rsh_ui32) : r(),
				m_sh_v128 == 0 ? rshl(object, m_rsh_ui32) : r()
			);

			break;
		}
		case f64:
		case i64:
		case ui64: {

			m_rsh_ui64 = r();
			m_sh_v128_64 = m_sh_v128 % 2;

			for (std::size_t i = 0; i < 4; ++i) {

				auto sw16 = reinterpret_cast<volatile std::uint16_t*>(&object)[i];
				m_ui64_split16[i] = rshl(sw16, m_rsh_ui64);
			}

			for (std::size_t i = 0; i < 2; ++i) {

				auto sw32 = reinterpret_cast<volatile std::uint32_t*>(&object)[i];
				m_ui64_split32[i] = rshl(sw32, m_rsh_ui64);
			}

			m_v128 = _mm_set_epi64x(

				m_sh_v128_64 == 0 ? rshl(object, m_rsh_ui64) : r() * r(),
				m_sh_v128_64 == 1 ? rshl(object, m_rsh_ui64) : r() * r()
			);

			break;
		}

		default: break;
		}
	}

#pragma endregion

	// ----------- Type Reconstruction (Inverse-Mutation) -----------
	// reconstruct_t: Reconstructs the original value from the mutated forms
	// Uses the selected mode and bit manipulations to recover the value
	template<typename _T>
	__forceinline const _T __fastcall reconstruct_t() noexcept {

		using r_T = std::remove_cv_t<_T>;

		volatile r_T r_T_inst = _T(NULL);

		if (reconstruct_mode) {

			for (std::size_t i = 0; i < (sizeof(T) * 8); ++i)
				r_T_inst |= static_cast<r_T>(original_set_map[i]) << i;
		}
		else {

			switch (base_type) {

			case i8:
			case ui8: {

				switch (rec_ui8_mode) {

				case 0: {

					r_T_inst = m_ui16 >> m_sh_16;
					break;
				}
				case 1: {

					r_T_inst = m_ui32 >> m_sh_32;
					break;
				}
				case 2: {

					r_T_inst = m_ui64 >> m_sh_64;
					break;
				}
				case 3: {

					alignas(0x10) std::uint32_t arr_v128[4];

					_mm_store_si128(reinterpret_cast<__m128i*>(arr_v128), m_v128);

					r_T_inst = static_cast<r_T>(arr_v128[m_sh_v128] >> m_sh_32);
					break;
				}
				default: break;
				}
				break;
			}
			case i16:
			case ui16: {

				switch (rec_ui16_mode) {

				case 0: {

					r_T_inst = m_ui32 >> m_sh_32;
					break;
				}
				case 1: {

					r_T_inst = m_ui64 >> m_sh_64;
					break;
				}
				case 2: {

					alignas(0x10) std::uint32_t arr_v128[4];

					_mm_store_si128(reinterpret_cast<__m128i*>(arr_v128), m_v128);

					r_T_inst = static_cast<r_T>(arr_v128[m_sh_v128] >> m_sh_32);
					break;
				}
				}

				break;
			}
			case f32:
			case i32:
			case ui32: {

				if (rec_ui32_mode) {

					r_T_inst = static_cast<r_T>(m_ui64 >> m_sh_64);
				}
				else {

					alignas(0x10) std::uint32_t arr_v128[4];

					_mm_store_si128(reinterpret_cast<__m128i*>(arr_v128), m_v128);

					r_T_inst = rshr(static_cast<r_T>(arr_v128[m_sh_v128]), m_rsh_ui32);
				}

				break;
			}
			case f64:
			case i64:
			case ui64: {

				switch (rec_ui64_mode) {

				case 0: {

					for (std::size_t i = 0; i < 2; ++i) {

						const auto sw32 = m_ui64_split32[i];
						reinterpret_cast<volatile std::uint32_t*>(&r_T_inst)[i] = rshr(sw32, m_rsh_ui64);
					}
					break;
				}
				case 1: {

					for (std::size_t i = 0; i < 4; ++i) {

						const auto sw16 = m_ui64_split16[i];
						reinterpret_cast<volatile std::uint16_t*>(&r_T_inst)[i] = rshr(sw16, m_rsh_ui64);
					}
					break;
				}
				case 2: {

					alignas(0x10) std::uint64_t arr_v128[2];
					_mm_store_si128(reinterpret_cast<__m128i*>(arr_v128), m_v128);

					r_T_inst = rshr(static_cast<std::remove_cv_t<_T>>(arr_v128[m_sh_v128_64 ? 0 : 1]), m_rsh_ui64);
					break;
				}
				}

				break;
			}

			default: break;
			}
		}

		return r_T_inst;
	};

public:

#pragma region Ctor / Secure Dtor, Accessors / Modulators

	// ----------- Public Interface -----------
	// cmut(const T object): Constructor, initializes and mutates the value
	// get(): Returns the reconstructed value, handling floating point and boolean types
	// set(): Mutates and stores a new value, updating the bit map and mutated forms
	// ~cmut(): Destructor, securely zeroes all sensitive memory
	// Operator overloads: Support arithmetic, bitwise, and assignment operations on the obfuscated value
	__forceinline cmut(const T object = T(NULL)) noexcept : base_type(get_mut_t(object)) {

		// C++ Mess Fixup. Fix the Standard Already - This Shouldn't be Necessary
		is_ctor_lock = true;

		set(object);

		is_ctor_lock = false;
	}

#pragma region Copy / Move Ctors

	// Copy Ctor
	cmut(const cmut<T>& other) noexcept {

		if (!is_ctor_lock)
			std::lock_guard<std::recursive_mutex> lock(cmut_mtx);
		if (!other.is_ctor_lock)
			std::lock_guard<std::recursive_mutex> lock(other.cmut_mtx);

		base_type = other.base_type;
		seed = other.seed;
		m_sh_16 = other.m_sh_16;
		m_sh_32 = other.m_sh_32;
		m_sh_64 = other.m_sh_64;
		m_sh_v128 = other.m_sh_v128;
		m_sh_v128_64 = other.m_sh_v128_64;
		std::memcpy(original_set_map, other.original_set_map, sizeof(original_set_map));
		m_ui16 = other.m_ui16;
		m_rsh_ui32 = other.m_rsh_ui32;
		m_ui32 = other.m_ui32;
		std::memcpy(m_ui64_split16, other.m_ui64_split16, sizeof(m_ui64_split16));
		std::memcpy(m_ui64_split32, other.m_ui64_split32, sizeof(m_ui64_split32));
		m_v128 = other.m_v128;
		m_rsh_ui64 = other.m_rsh_ui64;
		m_ui64 = other.m_ui64;
		reconstruct_mode = other.reconstruct_mode;
		rec_ui8_mode = other.rec_ui8_mode;
		rec_ui16_mode = other.rec_ui16_mode;
		rec_ui32_mode = other.rec_ui32_mode;
		rec_ui64_mode = other.rec_ui64_mode;
	}

	// Copy-Assignment
	cmut<T>& operator=(const cmut<T>& other) noexcept {

		if (this == &other) return *this;

		if (!is_ctor_lock)
			std::lock_guard<std::recursive_mutex> lock(cmut_mtx);
		if (!other.is_ctor_lock)
			std::lock_guard<std::recursive_mutex> lock(other.cmut_mtx);

		base_type = other.base_type;
		seed = other.seed;
		m_sh_16 = other.m_sh_16;
		m_sh_32 = other.m_sh_32;
		m_sh_64 = other.m_sh_64;
		m_sh_v128 = other.m_sh_v128;
		m_sh_v128_64 = other.m_sh_v128_64;
		std::memcpy(original_set_map, other.original_set_map, sizeof(original_set_map));
		m_ui16 = other.m_ui16;
		m_rsh_ui32 = other.m_rsh_ui32;
		m_ui32 = other.m_ui32;
		std::memcpy(m_ui64_split16, other.m_ui64_split16, sizeof(m_ui64_split16));
		std::memcpy(m_ui64_split32, other.m_ui64_split32, sizeof(m_ui64_split32));
		m_v128 = other.m_v128;
		m_rsh_ui64 = other.m_rsh_ui64;
		m_ui64 = other.m_ui64;
		reconstruct_mode = other.reconstruct_mode;
		rec_ui8_mode = other.rec_ui8_mode;
		rec_ui16_mode = other.rec_ui16_mode;
		rec_ui32_mode = other.rec_ui32_mode;
		rec_ui64_mode = other.rec_ui64_mode;

		return *this;
	}

	// Move Ctor
	cmut(cmut<T>&& other) noexcept {

		if (!is_ctor_lock)
			std::lock_guard<std::recursive_mutex> lock(cmut_mtx);

		base_type = std::move(other.base_type);
		seed = std::move(other.seed);
		m_sh_16 = std::move(other.m_sh_16);
		m_sh_32 = std::move(other.m_sh_32);
		m_sh_64 = std::move(other.m_sh_64);
		m_sh_v128 = std::move(other.m_sh_v128);
		m_sh_v128_64 = std::move(other.m_sh_v128_64);
		std::memcpy(original_set_map, other.original_set_map, sizeof(original_set_map));
		m_ui16 = std::move(other.m_ui16);
		m_rsh_ui32 = std::move(other.m_rsh_ui32);
		m_ui32 = std::move(other.m_ui32);
		std::memcpy(m_ui64_split16, other.m_ui64_split16, sizeof(m_ui64_split16));
		std::memcpy(m_ui64_split32, other.m_ui64_split32, sizeof(m_ui64_split32));
		m_v128 = std::move(other.m_v128);
		m_rsh_ui64 = std::move(other.m_rsh_ui64);
		m_ui64 = std::move(other.m_ui64);
		reconstruct_mode = std::move(other.reconstruct_mode);
		rec_ui8_mode = std::move(other.rec_ui8_mode);
		rec_ui16_mode = std::move(other.rec_ui16_mode);
		rec_ui32_mode = std::move(other.rec_ui32_mode);
		rec_ui64_mode = std::move(other.rec_ui64_mode);
	}

	// Move-Assignemnt
	cmut<T>& operator=(cmut<T>&& other) noexcept {

		if (this == &other) return *this;

		if (!is_ctor_lock)
			std::lock_guard<std::recursive_mutex> lock(cmut_mtx);

		base_type = std::move(other.base_type);
		seed = std::move(other.seed);
		m_sh_16 = std::move(other.m_sh_16);
		m_sh_32 = std::move(other.m_sh_32);
		m_sh_64 = std::move(other.m_sh_64);
		m_sh_v128 = std::move(other.m_sh_v128);
		m_sh_v128_64 = std::move(other.m_sh_v128_64);
		std::memcpy(original_set_map, other.original_set_map, sizeof(original_set_map));
		m_ui16 = std::move(other.m_ui16);
		m_rsh_ui32 = std::move(other.m_rsh_ui32);
		m_ui32 = std::move(other.m_ui32);
		std::memcpy(m_ui64_split16, other.m_ui64_split16, sizeof(m_ui64_split16));
		std::memcpy(m_ui64_split32, other.m_ui64_split32, sizeof(m_ui64_split32));
		m_v128 = std::move(other.m_v128);
		m_rsh_ui64 = std::move(other.m_rsh_ui64);
		m_ui64 = std::move(other.m_ui64);
		reconstruct_mode = std::move(other.reconstruct_mode);
		rec_ui8_mode = std::move(other.rec_ui8_mode);
		rec_ui16_mode = std::move(other.rec_ui16_mode);
		rec_ui32_mode = std::move(other.rec_ui32_mode);
		rec_ui64_mode = std::move(other.rec_ui64_mode);
		return *this;
	}

#pragma endregion

	__forceinline std::remove_cv_t<T> get() noexcept {

		if (!is_ctor_lock)
			std::lock_guard<std::recursive_mutex> lock(cmut_mtx);

		std::remove_cv_t<T> rval = std::remove_cv_t<T>(NULL);

		if constexpr (std::is_same_v<std::remove_cv_t<T>, float>)
			rval = std::bit_cast<float>(reconstruct_t<std::uint32_t>());
		else if constexpr (std::is_same_v<std::remove_cv_t<T>, double>)
			rval = std::bit_cast<double>(reconstruct_t<std::uint64_t>());
		else if constexpr (std::is_same_v<std::remove_cv_t<T>, long double>)
			rval = std::bit_cast<double>(reconstruct_t<std::uint64_t>());
		else if constexpr (std::is_same_v<std::remove_cv_t<T>, bool>)
			rval = static_cast<bool>(reconstruct_t<std::uint8_t>());
		else
			rval = reconstruct_t<std::remove_cv_t<T>>();

		return rval;
	}

	__forceinline const bool set(const std::remove_cv_t<T> object) noexcept {

		if (!is_ctor_lock)
			std::lock_guard<std::recursive_mutex> lock(cmut_mtx);

		std::mt19937 r(std::time(nullptr));

		if constexpr (std::is_same_v<std::remove_cv_t<T>, float>) {

			const volatile std::uint32_t v_obj = std::bit_cast<std::uint32_t>(object);

			for (std::size_t i = 0; i < (sizeof(T) * 8); ++i)
				original_set_map[i] = static_cast<bool>((v_obj >> i) & 0x1);

			deconstruct_t(v_obj, r);
		}
		else if constexpr (std::is_same_v<std::remove_cv_t<T>, double> || std::is_same_v<std::remove_cv_t<T>, long double>) {

			const volatile std::uint64_t v_obj = std::bit_cast<std::uint64_t>(object);

			for (std::size_t i = 0; i < (sizeof(T) * 8); ++i)
				original_set_map[i] = static_cast<bool>((v_obj >> i) & 0x1);

			deconstruct_t(v_obj, r);
		}
		else if constexpr (std::is_same_v<std::remove_cv_t<T>, bool>) {

			const volatile std::uint8_t v_obj = static_cast<std::uint8_t>(object);

			for (std::size_t i = 0; i < (sizeof(T) * 8); ++i)
				original_set_map[i] = static_cast<bool>((v_obj >> i) & 0x1);

			deconstruct_t(v_obj, r);
		}
		else if constexpr (std::is_pointer_v<std::remove_cv_t<T>>) {

			const volatile std::uintptr_t v_obj = static_cast<std::uintptr_t>(object);

			for (std::size_t i = 0; i < (sizeof(T) * 8); ++i)
				original_set_map[i] = static_cast<bool>((v_obj >> i) & 0x1);

			deconstruct_t(v_obj, r);
		}
		else {

			const volatile T v_obj = *const_cast<T*>(&object);

			for (std::size_t i = 0; i < (sizeof(T) * 8); ++i)
				original_set_map[i] = static_cast<bool>((v_obj >> i) & 0x1);

			if constexpr (std::is_pointer_v<std::remove_cv_t<T>>)
				deconstruct_t(reinterpret_cast<std::uintptr_t>(v_obj), r);
			else
				deconstruct_t(v_obj, r);

		}

		for (std::size_t i = (sizeof(T) * 8); i < sizeof(original_set_map); ++i)
			original_set_map[i] = static_cast<std::uint8_t>(r() & 0xFF);

		return true;
	}

	__forceinline ~cmut() noexcept {

		if (!is_ctor_lock)
			std::lock_guard<std::recursive_mutex> lock(cmut_mtx);

		m_sh_16 = NULL;
		m_sh_32 = NULL;
		m_sh_64 = NULL;
		m_sh_v128 = NULL;
		m_sh_v128_64 = NULL;

		SECURE_ZERO_MEMORY(original_set_map, sizeof(original_set_map));

		m_ui16 = NULL;

		m_ui32 = NULL;
		m_rsh_ui32 = NULL;

		m_ui64 = NULL;
		m_rsh_ui64 = NULL;
		SECURE_ZERO_MEMORY(m_ui64_split16, sizeof(m_ui64_split16));
		SECURE_ZERO_MEMORY(m_ui64_split32, sizeof(m_ui64_split32));

		m_v128 = _mm_setzero_si128();
	}

	__forceinline cmut __fastcall operator+(const std::remove_cv_t<T> value) const noexcept {
		return cmut(get() + value);
	}

	__forceinline cmut __fastcall operator-(const std::remove_cv_t<T> value) const noexcept {
		return cmut(get() - value);
	}

	__forceinline cmut __fastcall operator/(const std::remove_cv_t<T> value) const noexcept {
		return cmut(get() / value);
	}

	__forceinline cmut __fastcall operator*(const std::remove_cv_t<T> value) const noexcept {
		return cmut(get() * value);
	}

	__forceinline cmut __fastcall operator&(const std::remove_cv_t<T> value) const noexcept {
		return cmut(get() & value);
	}

	__forceinline cmut __fastcall operator|(const std::remove_cv_t<T> value) const noexcept {
		return cmut(get() | value);
	}

	__forceinline cmut __fastcall operator%(const std::remove_cv_t<T> value) const noexcept {
		return cmut(get() % value);
	}

	__forceinline cmut __fastcall operator^(const std::remove_cv_t<T> value) const noexcept {
		return cmut(get() ^ value);
	}

	__forceinline cmut __fastcall operator<<(const std::remove_cv_t<T> value) const noexcept {
		return cmut(get() << value);
	}

	__forceinline cmut __fastcall operator>>(const std::remove_cv_t<T> value) const noexcept {
		return cmut(get() >> value);
	}

	__forceinline cmut& __fastcall operator+=(const std::remove_cv_t<T> value) noexcept {
		set(get() + value, false);
		return *this;
	}

	__forceinline cmut& __fastcall operator-=(const std::remove_cv_t<T> value) noexcept {
		set(get() - value);
		return *this;
	}

	__forceinline cmut& __fastcall operator++() noexcept {
		return this->operator+=(1);
	}

	__forceinline cmut& __fastcall operator--() noexcept {
		return this->operator-=(1);
	}

	__forceinline cmut& __fastcall operator*=(const std::remove_cv_t<T> value) noexcept {
		set(get() * value);
		return *this;
	}

	__forceinline cmut& __fastcall operator/=(const std::remove_cv_t<T> value) noexcept {
		set(get() / value);
		return *this;
	}

	__forceinline cmut& __fastcall operator%=(const std::remove_cv_t<T> value) noexcept {
		set(get() % value);
		return *this;
	}

	__forceinline cmut& __fastcall operator^=(const std::remove_cv_t<T> value) noexcept {
		set(get() ^ value);
		return *this;
	}

	__forceinline cmut& __fastcall operator&=(const std::remove_cv_t<T> value) noexcept {
		set(get() & value);
		return *this;
	}

	__forceinline cmut& __fastcall operator|=(const std::remove_cv_t<T> value) noexcept {
		set(get() | value);
		return *this;
	}

	__forceinline cmut& __fastcall operator<<=(const std::remove_cv_t<T> value) noexcept {
		set(get() << value);
		return *this;
	}

	__forceinline cmut& __fastcall operator>>=(const std::remove_cv_t<T> value) noexcept {
		set(get() >> value, false);
		return *this;
	}

	__forceinline cmut& __fastcall operator=(const std::remove_cv_t<T> value) noexcept {
		set(value);
		return *this;
	}

	__forceinline __stdcall operator T() noexcept {
		return get();
	}

#pragma endregion

};

#endif