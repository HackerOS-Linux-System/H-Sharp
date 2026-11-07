#pragma once
#include "hsh_rt_decls.h"
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <string>
#include <tuple>
#include <functional>
#include <type_traits>
#include <utility>
#include <new>

namespace hs {

// ───────────────────────────── diagnostics ──────────────────────────────────
[[noreturn]] inline void die(const char* kind, const char* what, const char* loc) {
    fprintf(stderr, "%s: %s (at %s)\n", kind, what, loc ? loc : "?");
    fflush(stdout);
    exit(1);
}
inline void warn(const char* what, const char* loc) {
#ifdef HSH_STRICT_MEMORY
    die("error", what, loc);
#else
    // One line per distinct (message, location) pair — loops would otherwise flood stderr.
    static const char* seen_what[64]; static const char* seen_loc[64]; static int n = 0;
    for (int i = 0; i < n; i++) if (seen_what[i] == what && seen_loc[i] == loc) return;
    if (n < 64) { seen_what[n] = what; seen_loc[n] = loc; n++; }
    fprintf(stderr, "warning: %s (at %s)\n", what, loc ? loc : "?");
#endif
}

// ───────────────────────────── core value types ─────────────────────────────
struct Nil {
    template<class T> operator T*() const { return nullptr; }
};
static constexpr Nil nil{};

struct Str {
    const char* p;
    Str() : p("") {}
    Str(const char* s) : p(s ? s : "") {}
    Str(Nil);
    Str(char* s) : p(s ? s : "") {}
    Str(const std::string& s) : p(strdup(s.c_str())) {}
    operator const char*() const { return p; }
    const char* c_str() const { return p; }
    int64_t size() const;
};
namespace hs {
// strlen with a tiny pointer cache: scanning a multi-megabyte source with `s.len()` / `byte_at(s, i)` in a
// loop would otherwise be O(n²).  Only long strings are cached and the entry is validated on every hit.
inline int64_t fast_strlen(const char* p) {
    const char* e = (const char*)memchr(p, 0, 256);
    if (e) return (int64_t)(e - p);
    struct Ent { const char* p; int64_t n; };
    static thread_local Ent cache[4]; static thread_local unsigned next = 0;
    for (auto& c : cache) if (c.p == p && p[c.n] == 0 && p[c.n > 0 ? c.n - 1 : 0] != 0) return c.n;
    int64_t n = (int64_t)strlen(p);
    cache[next++ & 3] = Ent{p, n};
    return n;
}
}
inline int64_t Str::size() const { return hs::fast_strlen(p); }
inline Str operator+(Str a, Str b) { return Str(hsh_strcat(a.p, b.p)); }
inline Str& operator+=(Str& a, Str b) { a = a + b; return a; }
struct Any;

struct Any {
    int64_t v;
    Any() : v(0) {}
    Any(int64_t x) : v(x) {}
    Any(int x) : v(x) {}
    Any(Nil) : v(0) {}
    Any(Str s) : v((int64_t)(intptr_t)s.p) {}
    Any(const char* s) : v((int64_t)(intptr_t)s) {}
    Any(double d) { memcpy(&v, &d, 8); }
    Any(bool b) : v(b) {}
    template<class T> Any(T* p) : v((int64_t)(intptr_t)p) {}
    template<class T, class = std::enable_if_t<!std::is_same_v<T, Any>>> operator T() const;
};

inline Str::Str(Nil) : p("") {}
#define HS_ANY_OP(OP) \
    template<class T, class = std::enable_if_t<std::is_arithmetic_v<T>>> inline auto operator OP(Any a, T b) { return a.v OP (int64_t)b; } \
    template<class T, class = std::enable_if_t<std::is_arithmetic_v<T>>> inline auto operator OP(T a, Any b) { return (int64_t)a OP b.v; } \
    inline auto operator OP(Any a, Any b) { return a.v OP b.v; }
HS_ANY_OP(|) HS_ANY_OP(&) HS_ANY_OP(^) HS_ANY_OP(<<) HS_ANY_OP(>>) HS_ANY_OP(+) HS_ANY_OP(-) HS_ANY_OP(*) HS_ANY_OP(/) HS_ANY_OP(%)
HS_ANY_OP(<) HS_ANY_OP(>) HS_ANY_OP(<=) HS_ANY_OP(>=)
inline Str operator+(Str a, Any b) { return a + Str((const char*)(intptr_t)b.v); }
inline Str operator+(Any a, Str b) { return Str((const char*)(intptr_t)a.v) + b; }
struct Range { int64_t a, b; bool incl; };
struct NoMatch { template<class T> operator T() const { __builtin_trap(); } };

template<class T> struct Arr;
template<class T> struct Opt;
template<class T> struct is_arr : std::false_type {};
template<class T> struct is_arr<Arr<T>> : std::true_type {};
template<class T> struct is_opt : std::false_type {};
template<class T> struct is_opt<Opt<T>> : std::true_type {};
template<class T> struct is_tuple : std::false_type {};
template<class... T> struct is_tuple<std::tuple<T...>> : std::true_type {};
template<class T> struct is_fn : std::false_type {};
template<class T> struct is_fn<std::function<T>> : std::true_type {};

struct EnumBase {};
struct StructBase {};

template<class T> inline int64_t pack(const T& x);
template<class T> inline T unpack(int64_t v);

template<class T> struct Opt {
    bool has = false;
    T v{};
    Opt() {}
    Opt(Nil) {}
    Opt(const T& x) : has(true), v(x) {}
    template<class U, class = std::enable_if_t<std::is_convertible_v<U, T> && !is_opt<std::decay_t<U>>::value && !std::is_same_v<std::decay_t<U>, Nil>>>
    Opt(const U& x) : has(true), v((T)x) {}
    explicit operator bool() const { return has; }
    // H# narrows `T?` to `T` after a nil check (`if x != nil then x ..`, `let y: T = x`, `f(x)`, `a = x`);
    // the backend has no static types, so the narrowing happens here.
    operator const T&() const { return v; }
};

// `if c then a else b`: the two branches may have different C++ types (`Str` vs `Any`, `T` vs `Opt<T>`), which makes a
// plain `?:` ambiguous or ill-formed. Branches are lazy (lambdas); the result gets a common type.
template<class T> struct tern_tag { using type = T; };
template<class A, class B> constexpr auto tern_pick() {
    using a = std::decay_t<A>; using b = std::decay_t<B>;
    if constexpr (std::is_same_v<a, b>) return tern_tag<a>{};
    else if constexpr (std::is_same_v<a, Any>) return tern_tag<b>{};
    else if constexpr (std::is_same_v<b, Any>) return tern_tag<a>{};
    // `Arr<Str>` vs `Arr<Any>` (e.g. `[]` hinted as `[string]` vs `string_split`): both convert to each other, so `?:` is
    // ambiguous - prefer the concretely typed array
    else if constexpr (is_arr<a>::value && is_arr<b>::value && std::is_convertible_v<a, b> && std::is_convertible_v<b, a>) {
        if constexpr (std::is_same_v<a, Arr<Any>>) return tern_tag<b>{}; else return tern_tag<a>{};
    }
    else if constexpr (is_opt<a>::value && !is_opt<b>::value && std::is_convertible_v<b, a>) return tern_tag<a>{};
    else if constexpr (is_opt<b>::value && !is_opt<a>::value && std::is_convertible_v<a, b>) return tern_tag<b>{};
    else return tern_tag<decltype(true ? std::declval<A>() : std::declval<B>())>{};
}
template<class F, class G> inline auto tern(bool c, F&& f, G&& g) {
    using A = decltype(f()); using B = decltype(g());
    if constexpr (std::is_void_v<A> && std::is_void_v<B>) { if (c) f(); else g(); }
    else {
        using R = typename decltype(tern_pick<A, B>())::type;
        if (c) return R(f()); else return R(g());
    }
}

// `match opt is nil => .. v => .. end`: a bare binding arm after a `nil` arm sees the unwrapped value.
// Non-optional subjects pass through unchanged.
template<class T> inline const T& unopt(const Opt<T>& o) { return o.v; }
template<class T> inline T& unopt(Opt<T>& o) { return o.v; }
template<class T> inline T&& unopt(T&& x) { return std::forward<T>(x); }

template<class T> struct Arr {
    HshArray* a;
    Arr() : a(nullptr) {}
    Arr(HshArray* p) : a(p) {}
    Arr(Nil) : a(nullptr) {}
    template<class U, class = std::enable_if_t<!std::is_same_v<U, T>>> Arr(const Arr<U>& o) : a(o.a) {}
    int64_t len() const { return a ? a->len : 0; }
};
struct EmptyArr { template<class T> operator Arr<T>() const { return Arr<T>(hsh_array_new()); } };
template<class T> inline Arr<T> wrap_arr(HshArray* a) { return Arr<T>(a); }
using Bytes = Arr<int64_t>;

template<class T> inline int64_t pack(const T& x) {
    if constexpr (std::is_same_v<T, Str>) return (int64_t)(intptr_t)x.p;
    else if constexpr (std::is_same_v<T, Any>) return x.v;
    else if constexpr (std::is_same_v<T, bool>) return x ? 1 : 0;
    else if constexpr (std::is_floating_point_v<T>) { double d = (double)x; int64_t r; memcpy(&r, &d, 8); return r; }
    else if constexpr (std::is_pointer_v<T>) return (int64_t)(intptr_t)x;
    else if constexpr (std::is_integral_v<T>) return (int64_t)x;
    else if constexpr (is_arr<T>::value) return (int64_t)(intptr_t)x.a;
    else if constexpr (std::is_same_v<T, Nil>) return 0;
    else { // Opt / tuple / std::function → boxed copy
        T* b = new (hsh_alloc_ex(sizeof(T))) T(x);
        return (int64_t)(intptr_t)b;
    }
}
template<class T> inline T unpack(int64_t v) {
    if constexpr (std::is_same_v<T, Str>) return Str((const char*)(intptr_t)v);
    else if constexpr (std::is_same_v<T, Any>) { Any a; a.v = v; return a; }
    else if constexpr (std::is_same_v<T, bool>) return v != 0;
    else if constexpr (std::is_floating_point_v<T>) { double d; memcpy(&d, &v, 8); return (T)d; }
    else if constexpr (std::is_pointer_v<T>) return (T)(intptr_t)v;
    else if constexpr (std::is_integral_v<T>) return (T)v;
    else if constexpr (is_arr<T>::value) return T((HshArray*)(intptr_t)v);
    else { if (!v) return T{}; return *(T*)(intptr_t)v; }
}
template<class T, class> Any::operator T() const { return unpack<T>(v); }

// ───────────────── generic conversion used by C-runtime call wrappers ───────
template<class To, class From> inline To cv(const From& f) {
    if constexpr (std::is_same_v<To, From>) return f;
    else if constexpr (std::is_same_v<To, void>) return;
    else if constexpr (std::is_same_v<To, Str>) {
        if constexpr (std::is_pointer_v<From>) return Str((const char*)f); else return Str((const char*)(intptr_t)pack(f));
    }
    else if constexpr (std::is_same_v<From, Str>) {
        if constexpr (std::is_pointer_v<To>) return (To)f.p; else return unpack<To>((int64_t)(intptr_t)f.p);
    }
    else if constexpr (std::is_pointer_v<To> && is_arr<From>::value) return (To)f.a;
    else if constexpr (is_arr<To>::value && std::is_pointer_v<From>) return To((HshArray*)f);
    else if constexpr (std::is_pointer_v<To> && std::is_pointer_v<From>) return (To)f;
    else if constexpr (std::is_arithmetic_v<To> && std::is_arithmetic_v<From>) return (To)f;
    else return unpack<To>(pack(f));
}
template<class R, class... P, class... A>
inline R ccall(R (*f)(P...), const A&... a) { return f(cv<P>(a)...); }
// Result of a C-runtime call, shaped like the declared H# type D (arrays keep their C shape).
template<class D, class C> inline auto fin(C c) {
    if constexpr (std::is_same_v<C, HshArray*>) return Arr<Any>(c);
    else if constexpr (std::is_same_v<D, void>) return;
    else return cv<D>(c);
}

inline Str wrap(const char* s); inline Str wrap(char* s); inline bool wrap(bool b);
inline Arr<Any> wrap(HshArray* a); inline Any wrap(void* p); template<class T> inline T wrap(T v);
template<class D, class F, class... A> inline auto call_fin(F f, const A&... a) {
    using C = decltype(ccall(f, a...));
    if constexpr (std::is_void_v<C>) { ccall(f, a...); if constexpr (std::is_void_v<D>) return; else return D{}; }
    else return fin<D>(ccall(f, a...));
}
template<class F, class... A> inline auto call_wrap(F f, const A&... a) {
    using C = decltype(ccall(f, a...));
    if constexpr (std::is_void_v<C>) { ccall(f, a...); return; } else return wrap(ccall(f, a...));
}

// ───────────────────────────── string conversion ────────────────────────────
inline Str tostr(Str s) { return s; }
inline Str tostr(const char* s) { return Str(s); }
inline Str tostr(bool b) { return Str(b ? "true" : "false"); }
inline Str tostr(double d) { return Str(hsh_float_to_string(d)); }
inline Str tostr(float d) { return Str(hsh_float_to_string((double)d)); }
inline Str tostr(Nil) { return Str("nil"); }
inline Str tostr(Any a) { return Str(hsh_int_to_string(a.v)); }
template<class T, class = std::enable_if_t<std::is_integral_v<T> && !std::is_same_v<T, bool>>>
inline Str tostr(T i) { return Str(hsh_int_to_string((int64_t)i)); }
template<class T> inline Str tostr(T* p) { return Str(hsh_int_to_string((int64_t)(intptr_t)p)); }
template<class T> inline Str tostr(const Arr<T>& a);
template<class T> inline Str tostr(const Opt<T>& o) { return o.has ? tostr(o.v) : Str("nil"); }
template<class T> inline Str tostr(const Arr<T>& a) {
    Str out("[");
    for (int64_t i = 0; i < a.len(); i++) { if (i) out = out + Str(", "); out = out + tostr(unpack<T>(a.a->data[i])); }
    return out + Str("]");
}
template<class... T> inline Str tostr(const std::tuple<T...>& t) {
    Str out("("); bool first = true;
    std::apply([&](const auto&... e) { ((out = out + Str(first ? "" : ", ") + tostr(e), first = false), ...); }, t);
    return out + Str(")");
}

// ───────────────────────────── equality / ordering ──────────────────────────
inline bool eq(Str a, Str b) { return strcmp(a.p, b.p) == 0; }
template<class A, class B> inline bool eq(const A& a, const B& b);
template<class T> inline bool eq(const Opt<T>& a, Nil) { return !a.has; }
template<class T> inline bool eq(Nil, const Opt<T>& a) { return !a.has; }
inline bool eq(Nil, Nil) { return true; }
template<class T> inline bool eq(const Arr<T>& a, Nil) { return a.a == nullptr; }
template<class T> inline bool eq(T* a, Nil) { return a == nullptr; }
template<class T> inline bool eq(Nil, T* a) { return a == nullptr; }
inline bool eq(Any a, Nil) { return a.v == 0; }
inline bool eq(Str a, Nil) { return a.p == nullptr || *a.p == 0 ? false : false; }
template<class T> inline bool eq(const Opt<T>& a, const Opt<T>& b) { return a.has == b.has && (!a.has || eq(a.v, b.v)); }
template<class A, class B> inline bool eq(const A& a, const B& b) {
    if constexpr (std::is_pointer_v<A> && std::is_pointer_v<B>) {
        using P = std::remove_pointer_t<A>;
        if constexpr (std::is_base_of_v<EnumBase, P>) { if (a == b) return true; if (!a || !b) return false; return a->eq_(b); }
        else return (const void*)a == (const void*)b;
    }
    else if constexpr (is_opt<A>::value && !is_opt<B>::value) return a.has && eq(a.v, b);
    else if constexpr (!is_opt<A>::value && is_opt<B>::value) return b.has && eq(a, b.v);
    else if constexpr (std::is_same_v<A, Str> || std::is_same_v<B, Str>) return eq(cv<Str>(a), cv<Str>(b));
    else if constexpr (std::is_same_v<A, Any> || std::is_same_v<B, Any>) return pack(a) == pack(b);
    else if constexpr (is_arr<A>::value && is_arr<B>::value) return a.a == b.a;
    else if constexpr (is_tuple<A>::value) return a == b;
    else return a == b;
}
template<class A, class B> inline bool ne(const A& a, const B& b) { return !eq(a, b); }
inline bool lt(Str a, Str b) { return strcmp(a.p, b.p) < 0; }
inline bool lt(Any a, Any b) { return a.v < b.v; }
template<class A, class B> inline bool lt(const A& a, const B& b) { if constexpr (std::is_same_v<A, Str>) return strcmp(a.p, cv<Str>(b).p) < 0; else return a < b; }
template<class A, class B> inline bool gt(const A& a, const B& b) { return lt(b, a); }
template<class A, class B> inline bool le(const A& a, const B& b) { return !lt(b, a); }
template<class A, class B> inline bool ge(const A& a, const B& b) { return !lt(a, b); }

// ───────────────────────────── checked arithmetic ───────────────────────────
template<class A, class B> inline auto div(A a, B b, const char* loc) {
    using R = std::common_type_t<A, B>;
    if constexpr (std::is_integral_v<R>) {
        if (b == 0) { warn("integer division by zero (result 0)", loc); return (R)0; }
        if (b == -1) return (R)(0 - (typename std::make_unsigned<R>::type)a);
        return (R)(a / b);
    } else return (R)(a / b);
}
template<class A, class B> inline auto mod(A a, B b, const char* loc) {
    using R = std::common_type_t<A, B>;
    if constexpr (std::is_integral_v<R>) {
        if (b == 0) { warn("integer modulo by zero (result 0)", loc); return (R)0; }
        if (b == -1) return (R)0;
        return (R)(a % b);
    } else return (R)std::fmod((double)a, (double)b);
}

// ───────────────────────────── allocation helpers ───────────────────────────
template<class T> inline T* mk() { void* p = hsh_alloc_ex(sizeof(T)); memset(p, 0, sizeof(T)); return new (p) T(); }

// null-safe access: warns and hands back a zeroed scratch object
template<class T> inline T* p(T* x, const char* loc) {
    if (x) return x;
    warn("member access through a null struct pointer (using zeroed scratch object)", loc);
    static thread_local T scratch; scratch = T(); return &scratch;
}
template<class T> inline T* p(const Opt<T*>& x, const char* loc) { return p(x.has ? x.v : (T*)nullptr, loc); }

// `x.len` / `x.length` written as a field: a real field of a struct wins, otherwise the builtin length.
template<class T, class = void> struct has_len_field : std::false_type {};
template<class T> struct has_len_field<T, std::void_t<decltype(std::declval<T>().len)>> : std::true_type {};
template<class T> inline int64_t field_len(const T& x, const char* loc);
inline int64_t len(Str s);
// bounds already validated by the caller → no second strlen over the whole source
inline Str substr_unchecked(Str s, int64_t a, int64_t b) {
    if (a >= b) return Str("");
    size_t n = (size_t)(b - a);
    char* o = (char*)malloc(n + 1);
    memcpy(o, s.p + a, n); o[n] = 0;
    return Str(o);
}
// ───────────────────────────── arrays ───────────────────────────────────────
template<class T> inline int64_t len(const Arr<T>& a) { return a.len(); }
inline int64_t len(Str s) { return s.size(); }
template<class T> inline int64_t field_len(const T& x, const char* loc) {
    if constexpr (std::is_pointer_v<T>) {
        using P = std::remove_pointer_t<T>;
        if constexpr (has_len_field<P>::value) return (int64_t)p(x, loc)->len; else return len(x);
    } else return len(x);
}
template<class T> inline T idx(const Arr<T>& a, int64_t i, const char* loc) {
    if (!a.a || i < 0 || i >= a.a->len) { warn("array index out of bounds (read yields zero value)", loc); return T{}; }
    return unpack<T>(a.a->data[i]);
}
inline Str idx(Str s, int64_t i, const char* loc) {
    int64_t n = s.size();
    if (i < 0 || i >= n) { warn("string index out of bounds (read yields \"\")", loc); return Str(""); }
    return substr_unchecked(s, i, i + 1);
}
inline Str idx(Str s, Range r, const char* loc) {
    int64_t n = s.size(), a = r.a, b = r.incl ? r.b + 1 : r.b;
    if (a < 0 || b > n || a > b) { warn("string slice out of bounds (clamped)", loc); if (a < 0) a = 0; if (b > n) b = n; if (a > b) a = b; }
    return substr_unchecked(s, a, b);
}
template<class T> inline Arr<T> idx(const Arr<T>& s, Range r, const char* loc) {
    int64_t n = s.len(), a = r.a, b = r.incl ? r.b + 1 : r.b;
    if (a < 0 || b > n || a > b) { warn("array slice out of bounds (clamped)", loc); if (a < 0) a = 0; if (b > n) b = n; if (a > b) a = b; }
    return Arr<T>(hsh_array_slice(s.a, a, b));
}
template<class T, class V> inline void aset(const Arr<T>& a, int64_t i, const V& v, const char* loc) {
    if (!a.a || i < 0 || i >= a.a->len) { warn("array index out of bounds (write dropped)", loc); return; }
    a.a->data[i] = pack<T>((T)v);
}
template<class T, class V> inline void m_push_impl(Arr<T>& a, const V& v) {
    if (!a.a) a.a = hsh_array_new();
    if constexpr (is_opt<V>::value && !is_opt<T>::value) {   // pushing `T?` into `[T]`: nil → zero slot
        a.a = hsh_array_push(a.a, v.has ? pack<T>(v.v) : (int64_t)0);
    } else a.a = hsh_array_push(a.a, pack<T>(cv<T>(v)));
}
template<class T> inline Arr<T> concat(const Arr<T>& a, const Arr<T>& b) { return Arr<T>(hsh_array_concat(a.a, b.a)); }
template<class T> inline Arr<T> operator+(const Arr<T>& a, const Arr<T>& b) { return concat(a, b); }
template<class T> inline bool arr_contains(const Arr<T>& a, const T& v) {
    for (int64_t i = 0; i < a.len(); i++) if (eq(unpack<T>(a.a->data[i]), v)) return true;
    return false;
}
template<class... T> inline auto arr_lit(const char* /*loc*/, T... xs) {
    using E = std::common_type_t<T...>;
    Arr<E> r; r.a = hsh_array_new();
    ((r.a = hsh_array_push(r.a, pack<E>((E)xs))), ...);
    return r;
}
template<class E, class... T> inline Arr<E> arr_lit_t(T... xs) {
    Arr<E> r; r.a = hsh_array_new();
    ((r.a = hsh_array_push(r.a, pack<E>((E)xs))), ...);
    return r;
}

// ─────────────── tuples: `.0` / `.1` access and construction ────────────────
template<size_t N, class T> inline decltype(auto) tget(T&& t) { return std::get<N>(std::forward<T>(t)); }
template<size_t N, class T> inline auto tget(const Opt<T>& t) { return std::get<N>(t.v); }
template<class... T> inline auto tup(T... xs) { return std::make_tuple(xs...); }

// ───────────────────────────── try (`?`) support ────────────────────────────
// `expr?`: nil / 0 → early-return the "zero" of the enclosing function's return type.
template<class T, class = void> struct has_try_ret : std::false_type {};
template<class T> struct has_try_ret<T*, std::void_t<decltype(std::declval<T>().try_fail_())>> : std::true_type {};
template<class T> inline bool try_fail(const Opt<T>& o) { return !o.has; }
template<class T, class = std::enable_if_t<has_try_ret<T*>::value>> inline bool try_fail(T* p) { return p->try_fail_(); }
template<class T> inline bool try_fail(const T& v) {
    if constexpr (std::is_integral_v<T> && !std::is_same_v<T, bool>) return v == 0;
    else if constexpr (std::is_pointer_v<T>) return v == nullptr;
    else if constexpr (std::is_same_v<T, Any>) return v.v == 0;
    else if constexpr (is_arr<T>::value) return v.a == nullptr;
    else return false;
}
template<class T> inline auto try_val(const Opt<T>& o) { return o.v; }
template<class T, class = std::enable_if_t<has_try_ret<T*>::value>> inline auto try_val(T* p) { return p->try_val_(); }
template<class T> inline const T& try_val(const T& v) { return v; }
template<class R> inline R try_ret();
template<class R, class T> inline R try_ret_for(const T& v) {
    if constexpr (std::is_pointer_v<T> && has_try_ret<T>::value) return v->template try_ret_<R>();
    else return try_ret<R>();
}
template<class R> inline R try_ret() { if constexpr (std::is_void_v<R>) return; else return R{}; }

// ───────────────────────────── async tasks ──────────────────────────────────
template<class T> struct Task { void* h; };
template<class T> inline void* task_thunk(void* p) {
    auto* f = (std::function<int64_t()>*)p;
    int64_t r = (*f)();
    delete f;
    return (void*)(intptr_t)r;
}
template<class T, class F> inline Task<T> spawn(F f) {
    auto* fn = new std::function<int64_t()>([f]() mutable -> int64_t {
        if constexpr (std::is_void_v<T>) { f(); return 0; } else return pack<T>(f());
    });
    return Task<T>{ hsh_task_spawn((void*)&task_thunk<T>, fn) };
}
template<class T> inline T await_(Task<T> t) {
    int64_t r = hsh_task_wait(t.h);
    if constexpr (std::is_void_v<T>) return; else return unpack<T>(r);
}
template<class T> inline T await_(T v) { return v; }   // `await` on a non-async value is the identity

// ───────────────────────────── generic enum constructor proxy ───────────────
template<template<class...> class E, int Tag, class... Args> struct EnumProxy {
    std::tuple<Args...> a;
    template<class... X> operator E<X...>*() const { auto* r = mk<E<X...>>(); r->tag = Tag; r->set_(a); return r; }
};
template<template<class...> class E, int Tag, class... Args>
inline EnumProxy<E, Tag, std::decay_t<Args>...> enum_proxy(Args&&... a) { return {std::make_tuple(a...)}; }

// ───────────────────────────── C-return-value normalisation ─────────────────
inline Str wrap(const char* s) { return Str(s); }
inline Str wrap(char* s) { return Str(s); }
inline bool wrap(bool b) { return b; }
template<class T> inline T wrap(T v) {
    if constexpr (std::is_same_v<T, HshArray*>) return v;
    else return v;
}
inline Arr<Any> wrap(HshArray* a) { return Arr<Any>(a); }
inline Any wrap(void* p) { return Any(p); }

// ───────────────────────────── closures / function values ───────────────────
template<class T> using Fn = std::function<T>;

// ───────────────────────────── arena RAII (`@arena`, `unsafe arena`) ─────────
struct ArenaScope {
    HshArena* a;
    ArenaScope(int64_t kind, uint64_t cap) { a = hsh_arena_new_kind(cap, kind); hsh_arena_push_current(a); }
    ~ArenaScope() { hsh_arena_pop_current(); hsh_arena_free(a); }
    ArenaScope(const ArenaScope&) = delete; ArenaScope& operator=(const ArenaScope&) = delete;
};
// Values leaving an @arena function must outlive the arena: strings are copied
// to the malloc heap; anything else is returned as-is (and a warning is issued
// by the compiler's static audit when it can tell it points into the arena).
inline Str arena_escape(Str s) { return Str(strdup(s.p)); }
template<class T> inline T arena_escape(T v) { return v; }

// ───────────────────────────── @safety scope-end drop ────────────────────────
// Frees an owned array local when its scope ends (the compiler only emits this for arrays that provably never escape).
template<class T> struct DropArr {
    Arr<T>& r;
    explicit DropArr(Arr<T>& x) : r(x) {}
    ~DropArr() { if (r.a) { hsh_array_drop(r.a); r.a = nullptr; } }
    DropArr(const DropArr&) = delete; DropArr& operator=(const DropArr&) = delete;
};

// ───────────────────────────── @arc RAII ─────────────────────────────────────
struct ArcGuard {
    void* p; bool armed = true;
    explicit ArcGuard(void* ptr) : p(ptr) {}
    ~ArcGuard() { if (armed && p) hsh_rc_release(p); }
    void disarm() { armed = false; }
    ArcGuard(const ArcGuard&) = delete; ArcGuard& operator=(const ArcGuard&) = delete;
};

// ───────────────────────────── test harness ──────────────────────────────────
struct TestState { int run = 0, failed = 0, skipped = 0; bool cur_failed = false; const char* cur = ""; };
inline TestState& tstate() { static TestState s; return s; }
inline void tfail(const char* msg) {
    TestState& t = tstate(); t.cur_failed = true;
    fprintf(stderr, "    assertion failed in %s: %s\n", t.cur, msg);
}

} // namespace hs

using hs::Str; using hs::Any; using hs::Arr; using hs::Opt; using hs::Bytes;

// ═════════════════════════════════════════════════════════════════════════════
// Builtin functions (called from generated code as `hs_b_<name>`)
// Hand-written ones live here; thin wrappers around the C runtime for the
// remaining names are generated per program from the builtin registry.
// ═════════════════════════════════════════════════════════════════════════════
inline void hs_b_write(Str s)   { hsh_println(s.p); }
inline void hs_b_writeln(Str s) { hsh_println(s.p); }
inline void hs_b_println(Str s) { hsh_println(s.p); }
inline void hs_b_print(Str s)   { hsh_print(s.p); }
template<class T> inline Str hs_b_to_string(const T& v) { return hs::tostr(v); }
inline Str hs_b_to_string() { return Str("0"); }
template<class T> inline int64_t hs_b_len(const T& v) { return hs::len(v); }
[[noreturn]] inline void hs_b_panic(Str m) { hsh_panic(m.p); __builtin_unreachable(); }
[[noreturn]] inline void hs_b_exit(int64_t c = 0) { fflush(stdout); exit((int)c); }
inline int64_t hs_b_to_int(Str s) { return hsh_atoll(s.p); }
inline int64_t hs_b_to_int(double d) { return (int64_t)d; }
inline int64_t hs_b_to_int(int64_t d) { return d; }
inline double  hs_b_to_float(Str s) { return hsh_atof(s.p); }
inline double  hs_b_to_float(int64_t i) { return (double)i; }
inline double  hs_b_to_float(double i) { return i; }
inline Str     hs_b_to_hex(int64_t v) { char* b = (char*)hsh_alloc_ex(32); snprintf(b, 32, "%llx", (unsigned long long)v); return Str(b); }
inline int64_t hs_b_to_int_from_hex(Str s) { return (int64_t)strtoll(s.p, nullptr, 16); }

// math -----------------------------------------------------------------------
inline double hs_b_sin(double x) { return std::sin(x); }
inline double hs_b_cos(double x) { return std::cos(x); }
inline double hs_b_tan(double x) { return std::tan(x); }
inline double hs_b_sqrt(double x) { return std::sqrt(x); }
inline double hs_b_floor(double x) { return std::floor(x); }
inline double hs_b_ceil(double x) { return std::ceil(x); }
inline double hs_b_pow(double a, double b) { return std::pow(a, b); }
inline double hs_b_abs(double x) { return std::fabs(x); }
inline int64_t hs_b_abs(int64_t x) { return x < 0 ? -x : x; }
inline int64_t hs_b_min(int64_t a, int64_t b) { return a < b ? a : b; }
inline int64_t hs_b_max(int64_t a, int64_t b) { return a > b ? a : b; }
inline double hs_b_min(double a, double b) { return a < b ? a : b; }
inline double hs_b_max(double a, double b) { return a > b ? a : b; }

// strings --------------------------------------------------------------------
inline int64_t hs_b_string_len(Str s) { return s.size(); }
inline Str hs_b_string_at(Str s, int64_t i) { return hs::idx(s, i, "string_at"); }
inline Str hs_b_string_slice(Str s, int64_t a, int64_t b) { return hs::idx(s, hs::Range{a, b, false}, "string_slice"); }
inline bool hs_b_starts_with(Str s, Str p) { return strncmp(s.p, p.p, strlen(p.p)) == 0; }
inline bool hs_b_ends_with(Str s, Str p) { size_t a = strlen(s.p), b = strlen(p.p); return b <= a && strcmp(s.p + a - b, p.p) == 0; }
inline bool hs_b_contains(Str s, Str p) { return strstr(s.p, p.p) != nullptr; }
inline int64_t hs_b_string_find(Str s, Str p) { const char* r = strstr(s.p, p.p); return r ? (int64_t)(r - s.p) : -1; }
inline int64_t hs_b_string_rfind(Str s, Str p) {
    size_t n = strlen(p.p); int64_t best = -1; const char* c = s.p;
    while ((c = strstr(c, p.p))) { best = (int64_t)(c - s.p); c += (n ? 1 : 1); if (!*c && !n) break; }
    return best;
}
inline Str hs_b_string_repeat(Str s, int64_t n) { Str o(""); for (int64_t i = 0; i < n; i++) o = o + s; return o; }
inline Str hs_b_string_pad_right(Str s, int64_t w) { Str o = s; while (o.size() < w) o = o + Str(" "); return o; }
inline Str hs_b_string_trim_right(Str s) { int64_t n = s.size(); while (n > 0 && isspace((unsigned char)s.p[n - 1])) n--; return Str(hsh_substr(s.p, 0, n)); }

// arrays ---------------------------------------------------------------------
template<class T, class V> inline Arr<T> hs_b_array_push(Arr<T> a, V v) { hs::m_push_impl(a, v); return a; }
template<class T> inline int64_t hs_b_array_len(const Arr<T>& a) { return a.len(); }
template<class T> inline int64_t hs_b_array_count(const Arr<T>& a) { return a.len(); }
template<class T> inline T hs_b_array_get(const Arr<T>& a, int64_t i) { return hs::idx(a, i, "array_get"); }
template<class T, class V> inline Arr<T> hs_b_array_set(Arr<T> a, int64_t i, V v) { hs::aset(a, i, v, "array_set"); return a; }
template<class T, class V> inline bool hs_b_array_contains(const Arr<T>& a, const V& v) { return hs::arr_contains(a, (T)v); }
template<class T> inline Arr<T> hs_b_array_concat(const Arr<T>& a, const Arr<T>& b) { return hs::concat(a, b); }
template<class T> inline Arr<T> hs_b_array_new(T*) { return Arr<T>(hsh_array_new()); }

// raw pointers / arc / arena -------------------------------------------------
inline Any hs_b_arc_alloc(int64_t n) { return Any(hsh_rc_alloc((uint64_t)n)); }
inline void hs_b_arc_retain(Any p) { hsh_rc_retain((void*)(intptr_t)p.v); }
inline void hs_b_arc_release(Any p) { hsh_rc_release((void*)(intptr_t)p.v); }
inline int64_t hs_b_arc_count(Any p) { return hsh_rc_count((void*)(intptr_t)p.v); }
#define HS_PTR_RW(NAME, CT, HT) \
    inline HT hs_b_ptr_read_##NAME(Any p, int64_t off) { CT v; memcpy(&v, (char*)(intptr_t)p.v + off, sizeof(CT)); return (HT)v; } \
    inline void hs_b_ptr_write_##NAME(Any p, int64_t off, HT x) { CT v = (CT)x; memcpy((char*)(intptr_t)p.v + off, &v, sizeof(CT)); }
HS_PTR_RW(i64, int64_t, int64_t) HS_PTR_RW(i32, int32_t, int64_t) HS_PTR_RW(i16, int16_t, int64_t)
HS_PTR_RW(i8, int8_t, int64_t)   HS_PTR_RW(f64, double, double)   HS_PTR_RW(f32, float, double)
inline Any  hs_b_ptr_read_ptr(Any p, int64_t off) { int64_t v; memcpy(&v, (char*)(intptr_t)p.v + off, 8); Any a; a.v = v; return a; }
inline void hs_b_ptr_write_ptr(Any p, int64_t off, Any x) { memcpy((char*)(intptr_t)p.v + off, &x.v, 8); }
inline bool hs_b_ptr_is_null(Any p) { return p.v == 0; }
inline Any  hs_b_ptr_add(Any p, int64_t off) { Any a; a.v = p.v + off; return a; }
inline int64_t hs_b_arena_checkpoint() { return hsh_arena_checkpoint(); }
inline void hs_b_arena_rewind(int64_t m) { hsh_arena_rewind(m); }
inline int64_t hs_b_arena_used() { return hsh_arena_used(); }
inline int64_t hs_b_arena_capacity() { return hsh_arena_capacity(); }

// process / env --------------------------------------------------------------
inline Arr<Str> hs_b_env_args() {
    Arr<Str> r; r.a = hsh_array_new();
    for (int i = 0; i < _hsh_argc; i++) r.a = hsh_array_push(r.a, hs::pack(Str(_hsh_argv[i])));
    return r;
}

// assertions (used by `h# test`; harmless in normal builds) ---------------------
template<class A, class B> inline void hs_b_assert_eq(const A& a, const B& b) {
    if (!hs::eq(a, b)) hs::tfail((std::string("assert_eq: left=") + hs::tostr(a).p + " right=" + hs::tostr(b).p).c_str());
}
template<class A, class B> inline void hs_b_assert_ne(const A& a, const B& b) {
    if (hs::eq(a, b)) hs::tfail((std::string("assert_ne: both=") + hs::tostr(a).p).c_str());
}
inline void hs_b_assert_true(bool b)  { if (!b) hs::tfail("assert_true"); }
inline void hs_b_assert_false(bool b) { if (b) hs::tfail("assert_false"); }
template<class T> inline void hs_b_assert_nil(const T& v) { if (!hs::eq(v, hs::nil)) hs::tfail("assert_nil"); }
template<class T> inline void hs_b_assert_not_nil(const T& v) { if (hs::eq(v, hs::nil)) hs::tfail("assert_not_nil"); }
inline void hs_b_assert_approx(double a, double b, double eps) { if (std::fabs(a - b) > eps) hs::tfail("assert_approx"); }
inline void hs_b_assert_contains(Str h, Str n) { if (!hs_b_contains(h, n)) hs::tfail("assert_contains"); }
inline void hs_b_assert_starts_with(Str h, Str n) { if (!hs_b_starts_with(h, n)) hs::tfail("assert_starts_with"); }
template<class T> inline void hs_b_assert_len(const Arr<T>& a, int64_t n) { if (a.len() != n) hs::tfail("assert_len"); }
inline void hs_b_fail(Str m) { hs::tfail(m.p); }
inline void hs_b_skip(Str why = Str()) { hs::tstate().skipped++; if (*why.p) fprintf(stderr, "    skipped %s: %s\n", hs::tstate().cur, why.p); }

// ── method-call dispatch (`x.name(args)` → hs_m_name(x, args)) ────────────────
// Built-in receivers; user `impl` methods add overloads in the generated unit.
template<class T> inline int64_t hs_m_len(const Arr<T>& a) { return a.len(); }
inline int64_t hs_m_len(Str s) { return s.size(); }
// an untyped local (`let w = words[i]`) is hs::Any; without this exact match `w.len()` is ambiguous as soon as a
// program has any other hs_m_len overload (T*, StringBuilder ...). Any holding a string is by far the common case.
inline int64_t hs_m_len(const Any& a) { return Str((const char*)(intptr_t)a.v).size(); }
template<class T> inline int64_t hs_m_length(const Arr<T>& a) { return a.len(); }
inline int64_t hs_m_length(Str s) { return s.size(); }
inline int64_t hs_m_length(const Any& a) { return Str((const char*)(intptr_t)a.v).size(); }
template<class T> inline int64_t hs_m_count(const Arr<T>& a) { return a.len(); }
template<class T, class V> inline void hs_m_push(Arr<T>& a, const V& v) { hs::m_push_impl(a, v); }
template<class T, class V> inline void hs_m_append(Arr<T>& a, const V& v) { hs::m_push_impl(a, v); }
template<class T> inline T hs_m_pop(Arr<T>& a) {
    if (!a.a || a.a->len == 0) { hs::warn("pop() on an empty array (yields zero value)", "pop"); return T{}; }
    T v = hs::unpack<T>(a.a->data[a.a->len - 1]); a.a->len--; return v;
}
template<class T, class V> inline bool hs_m_contains(const Arr<T>& a, const V& v) { return hs::arr_contains(a, (T)v); }
inline bool hs_m_contains(Str s, Str p) { return hs_b_contains(s, p); }
template<class T> inline T hs_m_get(const Arr<T>& a, int64_t i) { return hs::idx(a, i, "get"); }
template<class T> inline void hs_m_remove(Arr<T>& a, int64_t i) { if (a.a) hsh_array_remove(a.a, i); }
inline bool hs_m_starts_with(Str s, Str p) { return hs_b_starts_with(s, p); }
inline bool hs_m_ends_with(Str s, Str p) { return hs_b_ends_with(s, p); }
inline int64_t hs_m_index_of(Str s, Str p) { return hs_b_string_find(s, p); }
inline int64_t hs_m_parse_int(Str s) { return hsh_atoll(s.p); }
inline double hs_m_round(double d) { return std::round(d); }
inline double hs_m_floor(double d) { return std::floor(d); }
inline double hs_m_ceil(double d) { return std::ceil(d); }
inline double hs_m_sqrt(double d) { return std::sqrt(d); }
inline double hs_m_abs(double d) { return std::fabs(d); }
inline int64_t hs_m_abs(int64_t d) { return d < 0 ? -d : d; }

// ── aliases & extra hand-written builtins ───────────────────────────────────
#define HS_ALIAS(NEW, OLD) template<class... A> inline auto hs_b_##NEW(A&&... a) -> decltype(hs_b_##OLD(std::forward<A>(a)...)) { return hs_b_##OLD(std::forward<A>(a)...); }
HS_ALIAS(math_sqrt, sqrt) HS_ALIAS(math_floor, floor) HS_ALIAS(math_ceil, ceil) HS_ALIAS(math_sin, sin)
HS_ALIAS(math_cos, cos) HS_ALIAS(math_tan, tan) HS_ALIAS(math_pow, pow) HS_ALIAS(math_abs, abs)
HS_ALIAS(math_min, min) HS_ALIAS(math_max, max)
inline Str hs_b_str_join(Arr<Str> a, Str sep) { return Str(hsh_array_join(a.a, sep.p)); }
inline Str hs_b_env_home() { return Str(hsh_env_home()); }
inline Arr<Str> hs_b_string_chars(Str s) { Arr<Str> r; r.a = hsh_array_new(); for (int64_t i = 0; i < s.size(); i++) r.a = hsh_array_push(r.a, hs::pack(hs::idx(s, i, "chars"))); return r; }
inline Str hs_b_string_trim_start(Str s) { while (*s.p && isspace((unsigned char)*s.p)) s.p++; return s; }
inline Str hs_b_string_replace(Str s, Str from, Str to) { return Str(hsh_str_replace(s.p, from.p, to.p)); }
inline Str hs_b_string_replace_all(Str s, Str from, Str to) { return Str(hsh_str_replace(s.p, from.p, to.p)); }
inline Str hs_b_exec(Str c) { return Str(hsh_exec1(c.p)); }
inline Str hs_b_exec(Str c, Str a) { return Str(hsh_exec2(c.p, a.p)); }
inline Str hs_b_exec(Str c, Str a, Str b) { return Str(hsh_exec3(c.p, a.p, b.p)); }
inline Str hs_b_exec(Str c, Str a, Str b, Str d) { return Str(hsh_exec4(c.p, a.p, b.p, d.p)); }
inline Str hs_b_db_query_bind(Str db, Str sql, Str b1) { return Str(hsh_sqlite_query_bind1(db.p, sql.p, b1.p)); }
inline Str hs_b_db_query_bind(Str db, Str sql, Str b1, Str b2) { return Str(hsh_sqlite_query_bind2(db.p, sql.p, b1.p, b2.p)); }
inline Str hs_b_db_query_bind(Str db, Str sql, Str b1, Str b2, Str b3) { return Str(hsh_sqlite_query_bind3(db.p, sql.p, b1.p, b2.p, b3.p)); }
template<class T> inline T hs_b_array_pop(Arr<T>& a) { return hs_m_pop(a); }
inline hs::Opt<int64_t> hs_b_parse_int(Str s) {
    char* end = nullptr; const char* p = s.p; if (!*p) return hs::nil;
    long long v = strtoll(p, &end, 10); if (*end) return hs::nil; return (int64_t)v;
}
inline Arr<int64_t> hs_b_sort_ints(Arr<int64_t> a) { return Arr<int64_t>(hsh_sort_ints(a.a)); }
// comparator trampolines for sort_by / sort_by_key (C runtime wants a plain function pointer)
namespace hs { inline std::function<int64_t(int64_t, int64_t)>*& cmp_slot() { static thread_local std::function<int64_t(int64_t, int64_t)>* f = nullptr; return f; }
               inline int64_t cmp_tramp(int64_t a, int64_t b) { return (*cmp_slot())(a, b); } }
template<class T, class F> inline Arr<T> hs_b_sort_by(Arr<T> a, F f) {
    std::function<int64_t(int64_t, int64_t)> w = [&](int64_t x, int64_t y) -> int64_t { return (int64_t)f(hs::unpack<T>(x), hs::unpack<T>(y)); };
    auto* saved = hs::cmp_slot(); hs::cmp_slot() = &w;
    Arr<T> r(hsh_sort_by(a.a, &hs::cmp_tramp)); hs::cmp_slot() = saved; return r;
}
template<class T, class F> inline Arr<T> hs_b_sort_by_key(Arr<T> a, F f) {
    std::function<int64_t(int64_t, int64_t)> w = [&](int64_t x, int64_t y) -> int64_t { auto kx = f(hs::unpack<T>(x)), ky = f(hs::unpack<T>(y)); return hs::lt(kx, ky) ? -1 : (hs::lt(ky, kx) ? 1 : 0); };
    auto* saved = hs::cmp_slot(); hs::cmp_slot() = &w;
    Arr<T> r(hsh_sort_by(a.a, &hs::cmp_tramp)); hs::cmp_slot() = saved; return r;
}

// `std/sort.h#` calls `__builtin_sort_by(arr, cmp)` / `__builtin_sort_by_key(arr, key)`. The generic registry wrapper turned the
// std::function into a "function pointer" by boxing it on the heap (hs::cv -> unpack<fnptr>(pack(f))) and the C sorter then jumped into
// that heap object (SIGSEGV). Both go through the trampolines instead.
template<class T, class F> inline Arr<T> hs_b___builtin_sort_by(Arr<T> a, F f) { return hs_b_sort_by(a, f); }
// keys compared as strings when both look like pointers, as signed ints otherwise (same rule as hsh_sort_by_key); stable
template<class T, class F> inline Arr<T> hs_b___builtin_sort_by_key(Arr<T> a, F f) {
    if (!a.a) return Arr<T>(hsh_array_new());
    int64_t n = a.a->len;
    if (n < 2) return a;
    int64_t* keys = (int64_t*)malloc((size_t)n * sizeof(int64_t));
    int64_t* idx  = (int64_t*)malloc((size_t)n * sizeof(int64_t));
    int64_t* out  = (int64_t*)malloc((size_t)n * sizeof(int64_t));
    if (!keys || !idx || !out) { free(keys); free(idx); free(out); return a; }
    auto looks_ptr = [](int64_t v) { return (uint64_t)v > 0x10000ULL && (uint64_t)v < 0x7ffffffffffeULL; };
    for (int64_t i = 0; i < n; i++) { keys[i] = hs::pack(f(hs::unpack<T>(a.a->data[i]))); idx[i] = i; }
    for (int64_t i = 1; i < n; i++) {
        int64_t cur = idx[i], j = i;
        while (j > 0) {
            int64_t k1 = keys[idx[j-1]], k2 = keys[cur];
            bool gt = (looks_ptr(k1) && looks_ptr(k2)) ? (strcmp((const char*)(uintptr_t)k1, (const char*)(uintptr_t)k2) > 0) : (k1 > k2);
            if (!gt) break;
            idx[j] = idx[j-1]; j--;
        }
        idx[j] = cur;
    }
    for (int64_t i = 0; i < n; i++) out[i] = a.a->data[idx[i]];
    memcpy(a.a->data, out, (size_t)n * sizeof(int64_t));
    free(keys); free(idx); free(out);
    return a;
}

// ── C++-implemented builtins that never had a C symbol ────────────────────────
inline Str hs_b_string_upper(Str s) { return Str(hsh_to_upper(s.p)); }
inline Str hs_b_string_lower(Str s) { return Str(hsh_to_lower(s.p)); }
inline Bytes hs_b_string_to_bytes(Str s) {
    Bytes r; r.a = hsh_array_new();
    for (const unsigned char* c = (const unsigned char*)s.p; *c; ++c) r.a = hsh_array_push(r.a, (int64_t)*c);
    return r;
}
template<class T> inline void hs_b_array_remove(Arr<T>& a, int64_t i) { hs_m_remove(a, i); }
inline void hs_b_assert(bool c, Str msg = Str("assertion failed")) { if (!c) hsh_panic(msg.p); }
inline double hs_b_math_pi() { return 3.14159265358979323846; }
inline double hs_b_math_e() { return 2.71828182845904523536; }
inline double hs_b_math_tau() { return 6.28318530717958647692; }
inline double hs_b_math_fabs(double x) { return std::fabs(x); }
inline double hs_b_math_fmin(double a, double b) { return a < b ? a : b; }
inline double hs_b_math_fmax(double a, double b) { return a > b ? a : b; }
inline int64_t hs_b_min_int(int64_t a, int64_t b) { return a < b ? a : b; }
inline int64_t hs_b_max_int(int64_t a, int64_t b) { return a > b ? a : b; }
inline int64_t hs_b_math_clamp(int64_t v, int64_t lo, int64_t hi) { return v < lo ? lo : (v > hi ? hi : v); }
inline double hs_b_math_fclamp(double v, double lo, double hi) { return v < lo ? lo : (v > hi ? hi : v); }
inline int64_t hs_b_math_gcd(int64_t a, int64_t b) { if (a < 0) a = -a; if (b < 0) b = -b; while (b) { int64_t t = a % b; a = b; b = t; } return a; }
inline int64_t hs_b_math_lcm(int64_t a, int64_t b) { if (!a || !b) return 0; int64_t g = hs_b_math_gcd(a, b); int64_t r = a / g * b; return r < 0 ? -r : r; }
inline int64_t hs_b_math_ipow(int64_t b, int64_t e) { int64_t r = 1; if (e < 0) return 0; while (e) { if (e & 1) r *= b; b *= b; e >>= 1; } return r; }

// ── tcp / atomics / base64url / string helpers (C++ implementations; no C symbol existed) ─────────
#if !defined(_WIN32)
#include <sys/socket.h>
#include <netdb.h>
#include <unistd.h>
#include <mutex>
#include <map>
#include <string>
inline int64_t hs_b___builtin_tcp_connect(Str host, int64_t port) {
    struct addrinfo hints; memset(&hints, 0, sizeof hints); hints.ai_socktype = SOCK_STREAM; hints.ai_family = AF_UNSPEC;
    struct addrinfo* res = nullptr; char ps[16]; snprintf(ps, sizeof ps, "%lld", (long long)port);
    if (getaddrinfo(host.p, ps, &hints, &res) != 0) return -1;
    int fd = -1;
    for (struct addrinfo* r = res; r; r = r->ai_next) {
        fd = socket(r->ai_family, r->ai_socktype, r->ai_protocol);
        if (fd < 0) continue;
        if (connect(fd, r->ai_addr, r->ai_addrlen) == 0) break;
        close(fd); fd = -1;
    }
    freeaddrinfo(res);
    return fd;
}
inline bool hs_b___builtin_tcp_send(int64_t fd, Str data) {
    if (fd < 0) return false;
    const char* p = data.p; size_t left = strlen(p);
    while (left) { ssize_t n = send((int)fd, p, left, 0); if (n <= 0) return false; p += n; left -= (size_t)n; }
    return true;
}
inline Str hs_b___builtin_tcp_recv(int64_t fd, int64_t size) {
    if (fd < 0 || size <= 0) return Str("");
    char* buf = (char*)hsh_alloc_ex((uint64_t)size + 1);
    ssize_t n = recv((int)fd, buf, (size_t)size, 0);
    if (n <= 0) return Str("");
    buf[n] = 0; return Str(buf);
}
inline void hs_b___builtin_tcp_close(int64_t fd) { if (fd >= 0) close((int)fd); }
#endif
namespace hs { inline std::mutex& atomic_mu() { static std::mutex m; return m; }
               inline std::map<std::string, int64_t>& atomic_map() { static std::map<std::string, int64_t> m; return m; } }
inline int64_t hs_b___builtin_atomic_add(Str n, int64_t v) { std::lock_guard<std::mutex> g(hs::atomic_mu()); int64_t& r = hs::atomic_map()[n.p]; r += v; return r; }
inline int64_t hs_b___builtin_atomic_load(Str n) { std::lock_guard<std::mutex> g(hs::atomic_mu()); return hs::atomic_map()[n.p]; }
inline void hs_b___builtin_atomic_store(Str n, int64_t v) { std::lock_guard<std::mutex> g(hs::atomic_mu()); hs::atomic_map()[n.p] = v; }

namespace hs {
inline Str b64url_encode_raw(const unsigned char* d, size_t n) {
    static const char* T = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    std::string o; size_t i = 0;
    for (; i + 2 < n; i += 3) { unsigned v = (d[i] << 16) | (d[i+1] << 8) | d[i+2]; o += T[v >> 18]; o += T[(v >> 12) & 63]; o += T[(v >> 6) & 63]; o += T[v & 63]; }
    if (i + 1 == n) { unsigned v = d[i] << 16; o += T[v >> 18]; o += T[(v >> 12) & 63]; }
    else if (i + 2 == n) { unsigned v = (d[i] << 16) | (d[i+1] << 8); o += T[v >> 18]; o += T[(v >> 12) & 63]; o += T[(v >> 6) & 63]; }
    return Str(o);
}
}
inline Str hs_b___builtin_base64url_encode(Str s) { return hs::b64url_encode_raw((const unsigned char*)s.p, strlen(s.p)); }
inline Str hs_b___builtin_base64url_decode(Str s) {
    auto val = [](char c) -> int { if (c >= 'A' && c <= 'Z') return c - 'A'; if (c >= 'a' && c <= 'z') return c - 'a' + 26; if (c >= '0' && c <= '9') return c - '0' + 52; if (c == '-' || c == '+') return 62; if (c == '_' || c == '/') return 63; return -1; };
    std::string o; unsigned acc = 0; int bits = 0;
    for (const char* c = s.p; *c; ++c) { int v = val(*c); if (v < 0) continue; acc = (acc << 6) | (unsigned)v; bits += 6; if (bits >= 8) { bits -= 8; char ch = (char)((acc >> bits) & 0xff); if (!ch) break; o += ch; } }
    return Str(o);
}
inline Str hs_b___builtin_hmac_sha256_b64url(Str key, Str msg) {
    Str hex = Str(hsh_crypto_hmac_sha256(key.p, msg.p));
    std::string raw; const char* h = hex.p;
    auto hv = [](char c) -> int { if (c >= '0' && c <= '9') return c - '0'; if (c >= 'a' && c <= 'f') return c - 'a' + 10; if (c >= 'A' && c <= 'F') return c - 'A' + 10; return -1; };
    for (size_t i = 0; h[i] && h[i+1]; i += 2) { int a = hv(h[i]), b = hv(h[i+1]); if (a < 0 || b < 0) break; raw += (char)(a * 16 + b); }
    return hs::b64url_encode_raw((const unsigned char*)raw.data(), raw.size());
}
inline Str hs_b___builtin_str_replace_all(Str s, Str from, Str to) { return Str(hsh_str_replace(s.p, from.p, to.p)); }
inline Str hs_b___builtin_str_reverse(Str s) { std::string t(s.p); return Str(std::string(t.rbegin(), t.rend())); }
inline bool hs_b___builtin_str_is_numeric(Str s) { if (!*s.p) return false; for (const char* c = s.p; *c; ++c) if (!isdigit((unsigned char)*c) && !(c == s.p && (*c == '-' || *c == '+') && c[1])) return false; return true; }
inline Str hs_b___builtin_str_trim_start(Str s) { return hs_b_string_trim_start(s); }
inline Str hs_b___builtin_str_trim_end(Str s) { return hs_b_string_trim_right(s); }

// ── bootstrap text primitives ────────────────────────────────────────────────────
inline int64_t hs_b_byte_at(Str s, int64_t i) { if (i < 0 || i >= s.size()) return -1; return (int64_t)(unsigned char)s.p[i]; }
inline Str hs_b_str_from_byte(int64_t n) { char* b = (char*)hsh_alloc_ex(2); b[0] = (char)n; b[1] = 0; return Str(b); }
inline bool hs_b_is_alpha_byte(int64_t c) { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || c >= 128; }
inline bool hs_b_is_digit_byte(int64_t c) { return c >= '0' && c <= '9'; }
inline bool hs_b_is_alnum_byte(int64_t c) { return hs_b_is_alpha_byte(c) || hs_b_is_digit_byte(c); }
inline bool hs_b_is_space_byte(int64_t c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }
inline int64_t hs_b_hash_str(Str s) { uint64_t h = 1469598103934665603ULL; for (const unsigned char* c = (const unsigned char*)s.p; *c; ++c) { h ^= *c; h *= 1099511628211ULL; } return (int64_t)(h & 0x7fffffffffffffffULL); }
namespace hs { struct StrBuf { std::string s; }; }
inline Any hs_b_sb_new() { return Any(new hs::StrBuf()); }
inline void hs_b_sb_push(Any b, Str s) { ((hs::StrBuf*)(intptr_t)b.v)->s.append(s.p); }
inline int64_t hs_b_sb_len(Any b) { return (int64_t)((hs::StrBuf*)(intptr_t)b.v)->s.size(); }
inline Str hs_b_sb_build(Any b) { return Str(((hs::StrBuf*)(intptr_t)b.v)->s); }
inline void hs_b_sb_clear(Any b) { ((hs::StrBuf*)(intptr_t)b.v)->s.clear(); }
template<class T> inline int64_t hs_b_hash_key(const T& k) {
    if constexpr (std::is_same_v<T, Str>) return hs_b_hash_str(k);
    else if constexpr (std::is_pointer_v<T>) {
        using P = std::remove_pointer_t<T>;
        if constexpr (std::is_base_of_v<hs::EnumBase, P>) return k ? (int64_t)(k->tag * 1315423911LL) & 0x7fffffffffffffffLL : 0;
        else return (int64_t)(((uintptr_t)k >> 3) * 2654435761ULL) & 0x7fffffffffffffffLL;
    }
    else if constexpr (std::is_floating_point_v<T>) { double d = (double)k; int64_t r; memcpy(&r, &d, 8); return r & 0x7fffffffffffffffLL; }
    else return (int64_t)((uint64_t)hs::pack(k) * 11400714819323198485ULL >> 1);
}

// ── methods on `T?` ────────────────────────────────────────────────────────────────
template<class T, class D> inline T hs_m_unwrap_or(const hs::Opt<T>& o, const D& d) { return o.has ? o.v : (T)d; }
template<class T> inline T hs_m_unwrap(const hs::Opt<T>& o) { if (!o.has) hsh_panic("unwrap() on nil"); return o.v; }
template<class T> inline bool hs_m_is_some(const hs::Opt<T>& o) { return o.has; }
template<class T> inline bool hs_m_is_none(const hs::Opt<T>& o) { return !o.has; }
