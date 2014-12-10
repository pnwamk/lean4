/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/placeholder.h"
#include "library/locals.h"
#include "library/explicit.h"
#include "library/reducible.h"
#include "library/coercion.h"
#include "library/class.h"
#include "library/definitional/equations.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/class.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"

namespace lean {
static environment declare_universe(parser & p, environment env, name const & n, bool local) {
    if (in_context(env) || local) {
        p.add_local_level(n, mk_param_univ(n), local);
    } else {
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        env = module::add_universe(env, full_n);
        if (!ns.is_anonymous())
            env = add_level_alias(env, n, full_n);
    }
    return env;
}

static environment universes_cmd_core(parser & p, bool local) {
    if (!p.curr_is_identifier())
        throw parser_error("invalid 'universes' command, identifier expected", p.pos());
    environment env = p.env();
    while (p.curr_is_identifier()) {
        name n = p.get_name_val();
        p.next();
        env = declare_universe(p, env, n, local);
    }
    return env;
}

static environment universe_cmd(parser & p) {
    if (p.curr_is_token(get_variables_tk())) {
        p.next();
        return universes_cmd_core(p, true);
    } else {
        bool local = false;
        if (p.curr_is_token(get_variable_tk())) {
            p.next();
            local = true;
        }
        name n = p.check_id_next("invalid 'universe' command, identifier expected");
        return declare_universe(p, p.env(), n, local);
    }
}

static environment universes_cmd(parser & p) {
    return universes_cmd_core(p, false);
}

bool parse_univ_params(parser & p, buffer<name> & ps) {
    if (p.curr_is_token(get_llevel_curly_tk())) {
        p.next();
        while (!p.curr_is_token(get_rcurly_tk())) {
            name l = p.check_id_next("invalid universe parameter, identifier expected");
            p.add_local_level(l, mk_param_univ(l));
            ps.push_back(l);
        }
        p.next();
        return true;
    } else{
        return false;
    }
}

void update_univ_parameters(buffer<name> & ls_buffer, name_set const & found, parser const & p) {
    unsigned old_sz = ls_buffer.size();
    found.for_each([&](name const & n) {
            if (std::find(ls_buffer.begin(), ls_buffer.begin() + old_sz, n) == ls_buffer.begin() + old_sz)
                ls_buffer.push_back(n);
        });
    std::sort(ls_buffer.begin(), ls_buffer.end(), [&](name const & n1, name const & n2) {
            return p.get_local_level_index(n1) < p.get_local_level_index(n2);
        });
}

enum class variable_kind { Constant, Parameter, Variable, Axiom };

static void check_parameter_type(parser & p, name const & n, expr const & type, pos_info const & pos) {
    for_each(type, [&](expr const & e, unsigned) {
            if (is_local(e) && p.is_local_variable(e))
                throw parser_error(sstream() << "invalid parameter declaration '" << n << "', it depends on " <<
                                   "variable '" << local_pp_name(e) << "'", pos);
            return true;
        });
}

static environment declare_var(parser & p, environment env,
                               name const & n, level_param_names const & ls, expr const & type,
                               variable_kind k, optional<binder_info> const & _bi, pos_info const & pos) {
    binder_info bi;
    if (_bi) bi = *_bi;
    if (k == variable_kind::Parameter || k == variable_kind::Variable) {
        if (k == variable_kind::Parameter) {
            check_in_context(p);
            check_parameter_type(p, n, type, pos);
        }
        if (p.get_local(n))
            throw parser_error(sstream() << "invalid parameter/variable declaration, '"
                               << n << "' has already been declared", pos);
        name u = p.mk_fresh_name();
        expr l = p.save_pos(mk_local(u, n, type, bi), pos);
        p.add_local_expr(n, l, k == variable_kind::Variable);
        return env;
    } else {
        lean_assert(k == variable_kind::Constant || k == variable_kind::Axiom);
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        if (k == variable_kind::Axiom) {
            env = module::add(env, check(env, mk_axiom(full_n, ls, type)));
            p.add_decl_index(full_n, pos, get_axiom_tk(), type);
        } else {
            env = module::add(env, check(env, mk_constant_assumption(full_n, ls, type)));
            p.add_decl_index(full_n, pos, get_variable_tk(), type);
        }
        if (!ns.is_anonymous())
            env = add_expr_alias(env, n, full_n);
        return env;
    }
}

/** \brief If we are in a section, then add the new local levels to it. */
static void update_local_levels(parser & p, level_param_names const & new_ls, bool is_variable) {
    for (auto const & l : new_ls)
        p.add_local_level(l, mk_param_univ(l), is_variable);
}

optional<binder_info> parse_binder_info(parser & p, variable_kind k) {
    optional<binder_info> bi = p.parse_optional_binder_info();
    if (bi && k != variable_kind::Parameter && k != variable_kind::Variable)
        parser_error("invalid binder annotation, it can only be used to declare variables/parameters", p.pos());
    return bi;
}

static void check_variable_kind(parser & p, variable_kind k) {
    if (in_context(p.env())) {
        if (k == variable_kind::Axiom || k == variable_kind::Constant)
            throw parser_error("invalid declaration, 'constant/axiom' cannot be used in contexts",
                               p.pos());
    } else {
        if (k == variable_kind::Parameter)
            throw parser_error("invalid declaration, 'parameter/hypothesis/conjecture' "
                               "can only be used in contexts", p.pos());
    }
}

static environment variable_cmd_core(parser & p, variable_kind k) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    optional<binder_info> bi = parse_binder_info(p, k);
    name n = p.check_id_next("invalid declaration, identifier expected");
    buffer<name> ls_buffer;
    if (p.curr_is_token(get_llevel_curly_tk()) && (k == variable_kind::Parameter || k == variable_kind::Variable))
        throw parser_error("invalid declaration, only constants/axioms can be universe polymorphic", p.pos());
    optional<parser::local_scope> scope1;
    if (k == variable_kind::Constant || k == variable_kind::Axiom)
        scope1.emplace(p);
    parse_univ_params(p, ls_buffer);
    expr type;
    if (!p.curr_is_token(get_colon_tk())) {
        buffer<expr> ps;
        unsigned rbp = 0;
        auto lenv = p.parse_binders(ps, rbp);
        p.check_token_next(get_colon_tk(), "invalid declaration, ':' expected");
        type = p.parse_scoped_expr(ps, lenv);
        type = Pi(ps, type, p);
    } else {
        p.next();
        type = p.parse_expr();
    }
    p.parse_close_binder_info(bi);
    level_param_names ls;
    if (ls_buffer.empty()) {
        ls = to_level_param_names(collect_univ_params(type));
    } else {
        update_univ_parameters(ls_buffer, collect_univ_params(type), p);
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    level_param_names new_ls;
    list<expr> ctx = p.locals_to_context();
    std::tie(type, new_ls) = p.elaborate_type(type, ctx);
    if (k == variable_kind::Variable || k == variable_kind::Parameter)
        update_local_levels(p, new_ls, k == variable_kind::Variable);
    return declare_var(p, p.env(), n, append(ls, new_ls), type, k, bi, pos);
}
static environment variable_cmd(parser & p) {
    return variable_cmd_core(p, variable_kind::Variable);
}
static environment axiom_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Axiom);
}
static environment constant_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Constant);
}
static environment parameter_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Parameter);
}

static environment variables_cmd_core(parser & p, variable_kind k) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    environment env = p.env();
    while (true) {
        optional<binder_info> bi = parse_binder_info(p, k);
        buffer<name> ids;
        while (!p.curr_is_token(get_colon_tk())) {
            name id = p.check_id_next("invalid parameters declaration, identifier expected");
            ids.push_back(id);
        }
        p.next();
        optional<parser::local_scope> scope1;
        if (k == variable_kind::Constant || k == variable_kind::Axiom)
            scope1.emplace(p);
        expr type = p.parse_expr();
        p.parse_close_binder_info(bi);
        level_param_names ls = to_level_param_names(collect_univ_params(type));
        list<expr> ctx = p.locals_to_context();
        for (auto id : ids) {
            // Hack: to make sure we get different universe parameters for each parameter.
            // Alternative: elaborate once and copy types replacing universes in new_ls.
            level_param_names new_ls;
            expr new_type;
            std::tie(new_type, new_ls) = p.elaborate_type(type, ctx);
            if (k == variable_kind::Variable || k == variable_kind::Parameter)
                update_local_levels(p, new_ls, k == variable_kind::Variable);
            new_ls = append(ls, new_ls);
            env = declare_var(p, env, id, new_ls, new_type, k, bi, pos);
        }
        if (!p.curr_is_token(get_lparen_tk()) && !p.curr_is_token(get_lcurly_tk()) &&
            !p.curr_is_token(get_ldcurly_tk()) && !p.curr_is_token(get_lbracket_tk()))
            break;
    }
    return env;
}
static environment variables_cmd(parser & p) {
    return variables_cmd_core(p, variable_kind::Variable);
}
static environment parameters_cmd(parser & p) {
    return variables_cmd_core(p, variable_kind::Parameter);
}
static environment constants_cmd(parser & p) {
    return variables_cmd_core(p, variable_kind::Constant);
}

struct decl_modifiers {
    bool               m_is_instance;
    bool               m_is_coercion;
    bool               m_is_reducible;
    optional<unsigned> m_priority;
    decl_modifiers():m_priority() {
        m_is_instance  = false;
        m_is_coercion  = false;
        m_is_reducible = false;
    }

    void parse(parser & p) {
        while (true) {
            auto pos = p.pos();
            if (p.curr_is_token(get_instance_tk())) {
                m_is_instance = true;
                p.next();
            } else if (p.curr_is_token(get_coercion_tk())) {
                auto pos = p.pos();
                p.next();
                if (in_context(p.env()))
                    throw parser_error("invalid '[coercion]' modifier, coercions cannot be defined in contexts", pos);
                m_is_coercion = true;
            } else if (p.curr_is_token(get_reducible_tk())) {
                m_is_reducible = true;
                p.next();
            } else if (auto it = parse_instance_priority(p)) {
                m_priority = *it;
                if (!m_is_instance)
                    throw parser_error("invalid '[priority]' occurrence, declaration must be marked as an '[instance]'", pos);
            } else {
                break;
            }
        }
    }
};

static void check_end_of_theorem(parser const & p) {
    if (!p.curr_is_command_like())
        throw parser_error("':=', '.', command, script, or end-of-file expected", p.pos());
}

static void erase_local_binder_info(buffer<expr> & ps) {
    for (expr & p : ps)
        p = update_local(p, binder_info());
}

static bool is_curr_with_or_comma(parser & p) {
    return p.curr_is_token(get_with_tk()) || p.curr_is_token(get_comma_tk());
}

expr parse_equations(parser & p, name const & n, expr const & type, buffer<expr> & auxs) {
    buffer<expr> eqns;
    {
        parser::local_scope scope1(p);
        parser::undef_id_to_local_scope scope2(p);
        lean_assert(is_curr_with_or_comma(p));
        expr f = mk_local(n, type);
        if (p.curr_is_token(get_with_tk())) {
            while (p.curr_is_token(get_with_tk())) {
                p.next();
                name g_name = p.check_id_next("invalid declaration, identifier expected");
                p.check_token_next(get_colon_tk(), "invalid declaration, ':' expected");
                expr g_type = p.parse_expr();
                expr g      = mk_local(g_name, g_type);
                auxs.push_back(g);
            }
        }
        p.check_token_next(get_comma_tk(), "invalid declaration, ',' expected");
        p.add_local(f);
        for (expr const & g : auxs)
            p.add_local(g);
        while (true) {
            expr lhs = p.parse_expr();
            p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
            expr rhs = p.parse_expr();
            eqns.push_back(mk_equation(lhs, rhs));
            if (!p.curr_is_token(get_comma_tk()))
                break;
            p.next();
        }
    }
    if (p.curr_is_token(get_wf_tk())) {
        p.next();
        expr Hwf = p.parse_expr();
        return mk_equations(eqns.size(), eqns.data(), Hwf);
    } else {
        return mk_equations(eqns.size(), eqns.data());
    }
}

// An Lean example is not really a definition, but we use the definition infrastructure to simulate it.
enum def_cmd_kind { Theorem, Definition, Example };

class definition_cmd_fn {
    parser &          m_p;
    environment       m_env;
    def_cmd_kind      m_kind;
    bool              m_is_opaque;
    bool              m_is_private;
    bool              m_is_protected;
    pos_info          m_pos;

    name              m_name;
    decl_modifiers    m_modifiers;
    name              m_real_name; // real name for this declaration
    buffer<name>      m_ls_buffer;
    buffer<expr>      m_aux_decls;
    expr              m_type;
    expr              m_value;
    level_param_names m_ls;
    pos_info          m_end_pos;

    expr              m_pre_type;
    expr              m_pre_value;

    bool is_definition() const { return m_kind == Definition; }
    unsigned start_line() const { return m_pos.first; }
    unsigned end_line() const { return m_end_pos.first; }

    void parse_name() {
        if (m_kind == Example)
            m_name = m_p.mk_fresh_name();
        else
            m_name = m_p.check_id_next("invalid declaration, identifier expected");
    }

    void parse_type_value() {
        // Parse universe parameters
        parser::local_scope scope1(m_p);
        parse_univ_params(m_p, m_ls_buffer);

        // Parse modifiers
        m_modifiers.parse(m_p);

        if (m_p.curr_is_token(get_assign_tk())) {
            auto pos = m_p.pos();
            m_p.next();
            m_type  = m_p.save_pos(mk_expr_placeholder(), pos);
            m_value = m_p.parse_expr();
        } else if (m_p.curr_is_token(get_colon_tk())) {
            m_p.next();
            auto pos = m_p.pos();
            m_type = m_p.parse_expr();
            if (is_curr_with_or_comma(m_p)) {
                m_value = parse_equations(m_p, m_name, m_type, m_aux_decls);
            } else if (!is_definition() && !m_p.curr_is_token(get_assign_tk())) {
                check_end_of_theorem(m_p);
                m_value = m_p.save_pos(mk_expr_placeholder(), pos);
            } else {
                m_p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                m_value = m_p.save_pos(m_p.parse_expr(), pos);
            }
        } else {
            buffer<expr> ps;
            optional<local_environment> lenv;
            bool last_block_delimited = false;
            lenv     = m_p.parse_binders(ps, last_block_delimited);
            auto pos = m_p.pos();
            if (m_p.curr_is_token(get_colon_tk())) {
                m_p.next();
                m_type = m_p.parse_scoped_expr(ps, *lenv);
                if (is_curr_with_or_comma(m_p)) {
                    m_value = parse_equations(m_p, m_name, m_type, m_aux_decls);
                } else if (!is_definition() && !m_p.curr_is_token(get_assign_tk())) {
                    check_end_of_theorem(m_p);
                    m_value = m_p.save_pos(mk_expr_placeholder(), pos);
                } else {
                    m_p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                    m_value = m_p.parse_scoped_expr(ps, *lenv);
                }
            } else {
                if (!last_block_delimited && !ps.empty() &&
                    !is_placeholder(mlocal_type(ps.back()))) {
                    throw parser_error("invalid declaration, ambiguous parameter declaration, "
                                       "(solution: put parentheses around parameters)",
                                       pos);
                }
                m_type = m_p.save_pos(mk_expr_placeholder(), m_p.pos());
                m_p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                m_value = m_p.parse_scoped_expr(ps, *lenv);
            }
            m_type  = Pi(ps, m_type, m_p);
            erase_local_binder_info(ps);
            m_value = Fun(ps, m_value, m_p);
        }
        m_end_pos = m_p.pos();
    }

    void mk_real_name() {
        if (m_is_private) {
            auto env_n  = add_private_name(m_env, m_name, optional<unsigned>(hash(m_pos.first, m_pos.second)));
            m_env       = env_n.first;
            m_real_name = env_n.second;
        } else {
            name const & ns = get_namespace(m_env);
            m_real_name     = ns + m_name;
        }
    }

    void parse() {
        parse_name();
        parse_type_value();
        if (m_p.used_sorry())
            m_p.declare_sorry();
        m_env = m_p.env();
        mk_real_name();
    }

    void process_locals() {
        if (m_p.has_locals()) {
            buffer<expr> locals;
            collect_locals(m_type, m_value, m_p, locals);
            m_type = Pi_as_is(locals, m_type, m_p);
            buffer<expr> new_locals;
            new_locals.append(locals);
            erase_local_binder_info(new_locals);
            m_value = Fun_as_is(new_locals, m_value, m_p);
            auto ps = collect_univ_params_ignoring_tactics(m_type);
            ps      = collect_univ_params_ignoring_tactics(m_value, ps);
            update_univ_parameters(m_ls_buffer, ps, m_p);
            remove_local_vars(m_p, locals);
            m_ls = to_list(m_ls_buffer.begin(), m_ls_buffer.end());
            levels local_ls = collect_local_nonvar_levels(m_p, m_ls);
            local_ls = remove_local_vars(m_p, local_ls);
            if (!locals.empty()) {
                expr ref = mk_local_ref(m_real_name, local_ls, locals);
                m_p.add_local_expr(m_name, ref);
            } else if (local_ls) {
                expr ref = mk_constant(m_real_name, local_ls);
                m_p.add_local_expr(m_name, ref);
            }
        } else {
            update_univ_parameters(m_ls_buffer, collect_univ_params(m_value, collect_univ_params(m_type)), m_p);
            m_ls = to_list(m_ls_buffer.begin(), m_ls_buffer.end());
        }
    }

    bool try_cache() {
        // We don't cache examples
        if (m_kind != Example && m_p.are_info_lines_valid(start_line(), end_line())) {
            // we only use the cache if the information associated with the line is valid
            if (auto it = m_p.find_cached_definition(m_real_name, m_type, m_value)) {
                optional<certified_declaration> cd;
                try {
                    level_param_names c_ls; expr c_type, c_value;
                    std::tie(c_ls, c_type, c_value) = *it;
                    if (m_kind == Theorem) {
                        cd = check(m_env, mk_theorem(m_real_name, c_ls, c_type, c_value));
                        if (!m_p.keep_new_thms()) {
                            // discard theorem
                            cd = check(m_env, mk_axiom(m_real_name, c_ls, c_type));
                        }
                    } else {
                        cd = check(m_env, mk_definition(m_env, m_real_name, c_ls, c_type, c_value, m_is_opaque));
                    }
                    if (!m_is_private)
                        m_p.add_decl_index(m_real_name, m_pos, m_p.get_cmd_token(), c_type);
                    m_env = module::add(m_env, *cd);
                    return true;
                } catch (exception&) {}
            }
        }
        return false;
    }

    void register_decl() {
        if (m_kind != Example) {
            if (!m_is_private)
                m_p.add_decl_index(m_real_name, m_pos, m_p.get_cmd_token(), m_type);
            if (m_real_name != m_name)
                m_env = add_expr_alias_rec(m_env, m_name, m_real_name);
            if (m_modifiers.m_is_instance) {
                bool persistent = true;
                if (m_modifiers.m_priority) {
                    #if defined(__GNUC__) && !defined(__CLANG__)
                    #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
                    #endif
                    m_env = add_instance(m_env, m_real_name, *m_modifiers.m_priority, persistent);
                } else {
                    m_env = add_instance(m_env, m_real_name, persistent);
                }
            }
            if (m_modifiers.m_is_coercion)
                m_env = add_coercion(m_env, m_real_name, m_p.ios());
            if (m_is_protected)
                m_env = add_protected(m_env, m_real_name);
            if (m_modifiers.m_is_reducible)
                m_env = set_reducible(m_env, m_real_name, reducible_status::On);
        }
    }

    void elaborate() {
        if (!try_cache()) {
            expr pre_type  = m_type;
            expr pre_value = m_value;
            level_param_names new_ls;
            m_p.remove_proof_state_info(m_pos, m_p.pos());
            if (!is_definition()) {
                // Theorems and Examples
                auto type_pos = m_p.pos_of(m_type);
                bool clear_pre_info = false; // we don't want to clear pre_info data until we process the proof.
                std::tie(m_type, new_ls) = m_p.elaborate_type(m_type, list<expr>(), clear_pre_info);
                check_no_metavar(m_env, m_real_name, m_type, true);
                m_ls = append(m_ls, new_ls);
                expr type_as_is = m_p.save_pos(mk_as_is(m_type), type_pos);
                if (!m_p.collecting_info() && m_kind == Theorem && m_p.num_threads() > 1) {
                    // Add as axiom, and create a task to prove the theorem.
                    // Remark: we don't postpone the "proof" of Examples.
                    m_p.add_delayed_theorem(m_env, m_real_name, m_ls, type_as_is, m_value);
                    m_env = module::add(m_env, check(m_env, mk_axiom(m_real_name, m_ls, m_type)));
                } else {
                    std::tie(m_type, m_value, new_ls) = m_p.elaborate_definition(m_name, type_as_is, m_value, m_is_opaque);
                    new_ls = append(m_ls, new_ls);
                    auto cd = check(m_env, mk_theorem(m_real_name, new_ls, m_type, m_value));
                    if (m_kind == Theorem) {
                        // Remark: we don't keep examples
                        if (!m_p.keep_new_thms()) {
                            // discard theorem
                            cd = check(m_env, mk_axiom(m_real_name, new_ls, m_type));
                        }
                        m_env = module::add(m_env, cd);
                        m_p.cache_definition(m_real_name, pre_type, pre_value, new_ls, m_type, m_value);
                    }
                }
            } else {
                std::tie(m_type, m_value, new_ls) = m_p.elaborate_definition(m_name, m_type, m_value, m_is_opaque);
                new_ls = append(m_ls, new_ls);
                m_env = module::add(m_env, check(m_env, mk_definition(m_env, m_real_name, new_ls,
                                                                      m_type, m_value, m_is_opaque)));
                m_p.cache_definition(m_real_name, pre_type, pre_value, new_ls, m_type, m_value);
            }
        }
    }

public:
    definition_cmd_fn(parser & p, def_cmd_kind kind, bool is_opaque, bool is_private, bool is_protected):
        m_p(p), m_env(m_p.env()), m_kind(kind), m_is_opaque(is_opaque),
        m_is_private(is_private), m_is_protected(is_protected),
        m_pos(p.pos()) {
        lean_assert(!(!is_definition() && !m_is_opaque));
        lean_assert(!(m_is_private && m_is_protected));
    }

    environment operator()() {
        parse();
        process_locals();
        elaborate();
        register_decl();
        return m_env;
    }
};

static environment definition_cmd_core(parser & p, def_cmd_kind kind, bool is_opaque, bool is_private, bool is_protected) {
    return definition_cmd_fn(p, kind, is_opaque, is_private, is_protected)();
}
static environment definition_cmd(parser & p) {
    return definition_cmd_core(p, Definition, false, false, false);
}
static environment opaque_definition_cmd(parser & p) {
    p.check_token_next(get_definition_tk(), "invalid 'opaque' definition, 'definition' expected");
    return definition_cmd_core(p, Definition, true, false, false);
}
static environment theorem_cmd(parser & p) {
    return definition_cmd_core(p, Theorem, true, false, false);
}
static environment example_cmd(parser & p) {
    return definition_cmd_core(p, Example, true, false, false);
}
static environment private_definition_cmd(parser & p) {
    def_cmd_kind kind = Definition;
    bool is_opaque  = false;
    if (p.curr_is_token_or_id(get_opaque_tk())) {
        is_opaque = true;
        p.next();
        p.check_token_next(get_definition_tk(), "invalid 'private' definition, 'definition' expected");
    } else if (p.curr_is_token_or_id(get_definition_tk())) {
        p.next();
    } else if (p.curr_is_token_or_id(get_theorem_tk())) {
        p.next();
        kind = Theorem;
        is_opaque  = true;
    } else {
        throw parser_error("invalid 'private' definition/theorem, 'definition' or 'theorem' expected", p.pos());
    }
    return definition_cmd_core(p, kind, is_opaque, true, false);
}
static environment protected_definition_cmd(parser & p) {
    def_cmd_kind kind = Definition;
    bool is_opaque  = false;
    if (p.curr_is_token_or_id(get_opaque_tk())) {
        is_opaque = true;
        p.next();
        p.check_token_next(get_definition_tk(), "invalid 'protected' definition, 'definition' expected");
    } else if (p.curr_is_token_or_id(get_definition_tk())) {
        p.next();
    } else if (p.curr_is_token_or_id(get_theorem_tk())) {
        p.next();
        kind       = Theorem;
        is_opaque  = true;
    } else {
        throw parser_error("invalid 'protected' definition/theorem, 'definition' or 'theorem' expected", p.pos());
    }
    return definition_cmd_core(p, kind, is_opaque, false, true);
}

static environment include_cmd_core(parser & p, bool include) {
    if (!p.curr_is_identifier())
        throw parser_error(sstream() << "invalid include/omit command, identifier expected", p.pos());
    while (p.curr_is_identifier()) {
        auto pos = p.pos();
        name n = p.get_name_val();
        p.next();
        if (!p.get_local(n))
            throw parser_error(sstream() << "invalid include/omit command, '" << n << "' is not a parameter/variable", pos);
        if (include) {
            if (p.is_include_variable(n))
                throw parser_error(sstream() << "invalid include command, '" << n << "' has already been included", pos);
            p.include_variable(n);
        } else {
            if (!p.is_include_variable(n))
                throw parser_error(sstream() << "invalid omit command, '" << n << "' has not been included", pos);
            p.omit_variable(n);
        }
    }
    return p.env();
}

static environment include_cmd(parser & p) {
    return include_cmd_core(p, true);
}

static environment omit_cmd(parser & p) {
    return include_cmd_core(p, false);
}

void register_decl_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("universe",     "declare a universe level", universe_cmd));
    add_cmd(r, cmd_info("universes",    "declare universe levels", universes_cmd));
    add_cmd(r, cmd_info("variable",     "declare a new variable", variable_cmd));
    add_cmd(r, cmd_info("parameter",    "declare a new parameter", parameter_cmd));
    add_cmd(r, cmd_info("constant",     "declare a new constant (aka top-level variable)", constant_cmd));
    add_cmd(r, cmd_info("axiom",        "declare a new axiom", axiom_cmd));
    add_cmd(r, cmd_info("variables",    "declare new variables", variables_cmd));
    add_cmd(r, cmd_info("parameters",   "declare new parameters", parameters_cmd));
    add_cmd(r, cmd_info("constants",    "declare new constants (aka top-level variables)", constants_cmd));
    add_cmd(r, cmd_info("definition",   "add new definition", definition_cmd));
    add_cmd(r, cmd_info("example",      "add new example", example_cmd));
    add_cmd(r, cmd_info("opaque",       "add new opaque definition", opaque_definition_cmd));
    add_cmd(r, cmd_info("private",      "add new private definition/theorem", private_definition_cmd));
    add_cmd(r, cmd_info("protected",    "add new protected definition/theorem", protected_definition_cmd));
    add_cmd(r, cmd_info("theorem",      "add new theorem", theorem_cmd));
    add_cmd(r, cmd_info("include",      "force section parameter/variable to be included", include_cmd));
    add_cmd(r, cmd_info("omit",         "undo 'include' command", omit_cmd));
}
}
