

# Defines a variant of the SOCWRForm which is appropriate for outer approximation

export SOCWROAPowerModel, SOCWROAForm

abstract type SOCWROAForm <: PMs.SOCWRForm end

const SOCWROAPowerModel = PMs.GenericPowerModel{SOCWROAForm}

"default SOCWROA constructor"
SOCWROAPowerModel(data::Dict{String,Any}; kwargs...) = PMs.GenericPowerModel(data, SOCWROAForm; kwargs...)

""
function PMs.objective_min_fuel_cost{T <: SOCWROAForm}(pm::GenericPowerModel{T})
    @assert !InfrastructureModels.ismultinetwork(pm.data)
    @assert !haskey(pm.data, "conductors")

    PMs.check_cost_models(pm)

    pg = var(pm, :pg)
    dc_p = var(pm, :p_dc)

    from_idx = Dict(arc[1] => arc for arc in ref(pm, :arcs_from_dc))

    pm.var[:pg_sqr] = Dict{Int, Any}()
    @expression(pm.model, gen_cost, 0)
    for (i, gen) in ref(pm, :gen)
        if gen["cost"][1] != 0.0
            pg_sqr = pm.var[:pg_sqr][i] = @variable(pm.model, 
                basename="pg_sqr",
                lowerbound = ref(pm, :gen, i, "pmin")^2,
                upperbound = ref(pm, :gen, i, "pmax")^2
            )
            @NLconstraint(pm.model, sqrt((2*pg[i])^2 + (pg_sqr-1)^2) <= pg_sqr+1)
            gen_cost = gen_cost + gen["cost"][1]*pg_sqr + gen["cost"][2]*pg[i] + gen["cost"][3]
        else
            gen_cost = gen_cost + gen["cost"][2]*pg[i] + gen["cost"][3]
        end
    end

    pm.var[:dc_p_sqr] = Dict{Int, Any}()
    @expression(pm.model, dcline_cost, 0)
    for (i, dcline) in ref(pm, :dcline)
        if dcline["cost"][1] != 0.0
            dc_p_sqr = pm.var[:dc_p_sqr][i] = @variable(pm.model, 
                basename="dc_p_sqr",
                lowerbound = ref(pm, :dcline, i, "pminf")^2,
                upperbound = ref(pm, :dcline, i, "pmaxf")^2
            )
            @NLconstraint(pm.model, sqrt((2*dc_p[from_idx[i]])^2 + (dc_p_sqr-1)^2) <= dc_p_sqr+1)
            dcline_cost = dcline_cost + dcline["cost"][1]*dc_p_sqr^2 + dcline["cost"][2]*dc_p[from_idx[i]] + dcline["cost"][3]
        else
            dcline_cost = dcline_cost + dcline["cost"][2]*dc_p[from_idx[i]] + dcline["cost"][3]
        end
    end

    return @objective(pm.model, Min, gen_cost + dcline_cost)
end


function PMs.constraint_voltage(pm::GenericPowerModel{T}, n::Int, h::Int) where T <: SOCWROAForm
    w  = var(pm, n, h,  :w)
    wr = var(pm, n, h, :wr)
    wi = var(pm, n, h, :wi)


    for (i,j) in ids(pm, n, :buspairs)
        @NLconstraint(pm.model, (wr[(i,j)]^2 + wi[(i,j)]^2)/w[j] <= w[i])
    end
end

function PMs.constraint_thermal_limit_from{T <: SOCWROAForm}(pm::GenericPowerModel{T}, n::Int, h::Int, f_idx, rate_a)
    p_fr = var(pm, n, h, :p, f_idx)
    q_fr = var(pm, n, h, :q, f_idx)
    @NLconstraint(pm.model, sqrt(p_fr^2 + q_fr^2) <= rate_a)
end

function PMs.constraint_thermal_limit_to{T <: SOCWROAForm}(pm::GenericPowerModel{T}, n::Int, h::Int, t_idx, rate_a)
    p_to = var(pm, n, h, :p, t_idx)
    q_to = var(pm, n, h, :q, t_idx)
    @NLconstraint(pm.model, sqrt(p_to^2 + q_to^2) <= rate_a)
end



# Defines a variant of the SOCWRForm which forces the NL solver path

export NLSOCWRPowerModel, NLSOCWROAForm

@compat abstract type NLSOCWROAForm <: PMs.SOCWRForm end

const NLSOCWRPowerModel = PMs.GenericPowerModel{NLSOCWROAForm}

"default NLSOCWROAForm constructor"
NLSOCWRPowerModel(data::Dict{String,Any}; kwargs...) = PMs.GenericPowerModel(data, NLSOCWROAForm; kwargs...)



# Defines a variant of the QCWRTriForm without the linking constraints

export QCWRTriNoLinkPowerModel, QCWRTriNoLinkForm

@compat abstract type QCWRTriNoLinkForm <: PMs.QCWRTriForm end

const QCWRTriNoLinkPowerModel = PMs.GenericPowerModel{QCWRTriNoLinkForm}

"default QC trilinear without linking constraint model constructor"
QCWRTriNoLinkPowerModel(data::Dict{String,Any}; kwargs...) = PMs.GenericPowerModel(data, QCWRTriNoLinkForm; kwargs...)

function PMs.constraint_voltage(pm::GenericPowerModel{T}, n::Int, c::Int) where T <: QCWRTriNoLinkForm
    v = var(pm, n, c, :vm)
    t = var(pm, n, c, :va)

    td = var(pm, n, c, :td)
    si = var(pm, n, c, :si)
    cs = var(pm, n, c, :cs)

    w = var(pm, n, c, :w)
    wr = var(pm, n, c, :wr)
    lambda_wr = var(pm, n, c, :lambda_wr)
    wi = var(pm, n, c, :wi)
    lambda_wi = var(pm, n, c, :lambda_wi)

    for (i,b) in ref(pm, n, :bus)
        InfrastructureModels.relaxation_sqr(pm.model, v[i], w[i])
    end

    for bp in ids(pm, n, :buspairs)
        i,j = bp
        @constraint(pm.model, t[i] - t[j] == td[bp])

        PMs.relaxation_sin(pm.model, td[bp], si[bp])
        PMs.relaxation_cos(pm.model, td[bp], cs[bp])
        InfrastructureModels.relaxation_trilinear(pm.model, v[i], v[j], cs[bp], wr[bp], lambda_wr[bp,:])
        InfrastructureModels.relaxation_trilinear(pm.model, v[i], v[j], si[bp], wi[bp], lambda_wi[bp,:])

        # this constraint is redudant and useful for debugging
        #InfrastructureModels.relaxation_complex_product(pm.model, w[i], w[j], wr[bp], wi[bp])
   end

   for (i,branch) in ref(pm, n, :branch)
        pair = (branch["f_bus"], branch["t_bus"])
        buspair = ref(pm, n, :buspairs, pair)

        # to prevent this constraint from being posted on multiple parallel branchs
        if buspair["branch"] == i
            PMs.constraint_power_magnitude_sqr(pm, i, nw=n, cnd=c)
            PMs.constraint_power_magnitude_link(pm, i, nw=n, cnd=c)
        end
    end

end



# Extending QCWRTriForm with voltage magnitude difference variables and constraints

export QCWRTriVPowerModel, QCWRTriVForm

@compat abstract type QCWRTriVForm <: PMs.QCWRTriForm end

const QCWRTriVPowerModel = PMs.GenericPowerModel{QCWRTriVForm}

"default QC trilinear without linking constraint model constructor"
QCWRTriVPowerModel(data::Dict{String,Any}; kwargs...) = PMs.GenericPowerModel(data, QCWRTriVForm; kwargs...)


function PMs.variable_multipliers{T <: QCWRTriVForm}(pm::GenericPowerModel{T})
    var(pm)[:lambda_wr] = @variable(pm.model,
    [bp in ids(pm, :buspairs), i=1:8], basename="lambda",
    lowerbound = 0, upperbound = 1)

    var(pm)[:lambda_wi] = @variable(pm.model,
    [bp in ids(pm, :buspairs), i=1:8], basename="lambda",
    lowerbound = 0, upperbound = 1)
end


# ref = PMs.build_ref(case)[:nw][0]

#    @variable(pm.model, va[i in keys(ref[:bus])])
#    @variable(pm.model, ref[:bus][i]["vmin"] <= vm[i in keys(ref[:bus])] <= ref[:bus][i]["vmax"], start=1.0)

#    @variable(pm.model, ref[:gen][i]["pmin"] <= pg[i in keys(ref[:gen])] <= ref[:gen][i]["pmax"])
#    @variable(pm.model, ref[:gen][i]["qmin"] <= qg[i in keys(ref[:gen])] <= ref[:gen][i]["qmax"])


function variable_voltage_magnitude_difference_neghboring_buses{T <: QCWRTriVForm}(pm::GenericPowerModel{T})
    var(pm)[:vd] = @variable(pm.model,
    [bp in ids(pm, :buspairs)], basename="vd",
    lowerbound = ref(pm, :buspairs, bp, "vdiff_min"),
    upperbound = ref(pm, :buspairs, bp, "vdiff_max")
    )
end

function variable_voltage_difference_product_voltage_from{T <: QCWRTriVForm}(pm::GenericPowerModel{T})
    buspairs = ref(pm, :buspairs)
    var(pm)[:vvv_fr] = @variable(pm.model,
    [bp in ids(pm, :buspairs)], basename="vvv_fr",
    lowerbound = min(buspairs[bp]["vm_fr_min"]*buspairs[bp]["vdiff_min"], buspairs[bp]["vm_fr_max"]*buspairs[bp]["vdiff_min"]),
    upperbound = max(buspairs[bp]["vm_fr_max"]*buspairs[bp]["vdiff_max"], buspairs[bp]["vm_fr_min"]*buspairs[bp]["vdiff_max"])
    )
end

function variable_voltage_difference_product_voltage_to{T <: QCWRTriVForm}(pm::GenericPowerModel{T})
    buspairs = ref(pm, :buspairs)
    var(pm)[:vvv_to] = @variable(pm.model,
    [bp in ids(pm, :buspairs)], basename="vvv_to",
    lowerbound = min(buspairs[bp]["vm_to_min"]*buspairs[bp]["vdiff_min"], buspairs[bp]["vm_to_max"]*buspairs[bp]["vdiff_min"]),
    upperbound = max(buspairs[bp]["vm_to_max"]*buspairs[bp]["vdiff_max"], buspairs[bp]["vm_to_min"]*buspairs[bp]["vdiff_max"])
    )
end

function variable_voltage_squared_product{T <: QCWRTriVForm}(pm::GenericPowerModel{T})
    buspairs = ref(pm,:buspairs)
    var(pm)[:w_squared] = @variable(pm.model,
    [bp in keys(buspairs)], basename="w_squared",
    lowerbound = (buspairs[bp]["vm_fr_min"])^2*(buspairs[bp]["vm_to_min"])^2,
    upperbound = (buspairs[bp]["vm_fr_max"])^2*(buspairs[bp]["vm_to_max"])^2
    )
end

function variable_voltage_magnitude_diff_sqr{T <: QCWRTriVForm}(pm::GenericPowerModel{T})
    buspairs = ref(pm, :buspairs)
    var(pm)[:vd_squared] = @variable(pm.model,
    [bp in keys(buspairs)], basename="vd_squared",
    lowerbound = 0,
    upperbound = max((buspairs[bp]["vdiff_min"])^2,(buspairs[bp]["vdiff_max"])^2)
    )
end

function PMs.variable_voltage(pm::GenericPowerModel{T}; kwargs...) where T <: QCWRTriVForm
    PMs.variable_voltage_angle(pm; kwargs...)
    PMs.variable_voltage_magnitude(pm; kwargs...)
    PMs.variable_voltage_magnitude_sqr(pm; kwargs...)
    PMs.variable_voltage_product(pm; kwargs...)
    PMs.variable_voltage_angle_difference(pm; kwargs...)
    PMs.variable_voltage_magnitude_product(pm; kwargs...)
    PMs.variable_multipliers(pm; kwargs...)
    PMs.variable_cosine(pm; kwargs...)
    PMs.variable_sine(pm; kwargs...)
    PMs.variable_current_magnitude_sqr(pm; kwargs...)

    variable_voltage_magnitude_difference_neghboring_buses(pm; kwargs...)
    variable_voltage_squared_product(pm; kwargs...)
    variable_voltage_difference_product_voltage_from(pm; kwargs...)
    variable_voltage_difference_product_voltage_to(pm; kwargs...)
    variable_voltage_magnitude_diff_sqr(pm; kwargs...)
end


function PMs.constraint_voltage(pm::GenericPowerModel{T}, n::Int, c::Int) where T <: QCWRTriVForm
    v = var(pm, n, c, :vm)
    t = var(pm, n, c, :va)

    td = var(pm, n, c, :td)
    si = var(pm, n, c, :si)
    cs = var(pm, n, c, :cs)

    w = var(pm, n, c, :w)
    wr = var(pm, n, c, :wr)
    lambda_wr = var(pm, n, c, :lambda_wr)
    wi = var(pm, n, c, :wi)
    lambda_wi = var(pm, n, c, :lambda_wi)

    vd = var(pm, n, c, :vd)
    vv = var(pm, n, c, :vv)
    vvv_fr = var(pm, n, c, :vvv_fr)
    vvv_to = var(pm, n, c, :vvv_to)
    w_squared = var(pm, n ,c ,:w_squared)
    vd_squared = var(pm, n ,c , :vd_squared)

    for (i,b) in ref(pm, n, :bus)
        InfrastructureModels.relaxation_sqr(pm.model, v[i], w[i])
    end

    for bp in ids(pm, n, :buspairs)
        i,j = bp
        @constraint(pm.model, t[i] - t[j] == td[bp])

        @constraint(pm.model, v[i] - v[j] == vd[bp])


        PMs.relaxation_sin(pm.model, td[bp], si[bp])
        PMs.relaxation_cos(pm.model, td[bp], cs[bp])
        InfrastructureModels.relaxation_trilinear(pm.model, v[i], v[j], cs[bp], wr[bp], lambda_wr[bp,:])
        InfrastructureModels.relaxation_trilinear(pm.model, v[i], v[j], si[bp], wi[bp], lambda_wi[bp,:])
        PMs.relaxation_tighten_vv(pm.model, v[i], v[j], lambda_wr[bp,:], lambda_wi[bp,:])
        # this constraint is redudant and useful for debugging
        #InfrastructureModels.relaxation_complex_product(pm.model, w[i], w[j], wr[bp], wi[bp])

        InfrastructureModels.relaxation_product(pm.model, v[i], v[j], vv[bp])
        InfrastructureModels.relaxation_product(pm.model, v[i], vd[bp], vvv_fr[bp])
        InfrastructureModels.relaxation_product(pm.model, v[j], vd[bp], vvv_to[bp])
        InfrastructureModels.relaxation_product(pm.model, w[i], w[j], w_squared[bp])
    end


    orientations = Set()
        for (i, branch) in ref(pm, n, :branch)
                orientation = (branch["f_bus"], branch["t_bus"])
                orientation_rev = (branch["t_bus"], branch["f_bus"])

                if in(orientation_rev, orientations)
                        warn(LOGGER, "reversing the orientation of branch $(i) $(orientation) to be consistent with other parallel branches")
                        branch_orginal = copy(branch)

                        branch["vdiff_min"] = -branch_orginal["vdiff_max"]
                        branch["vdiff_max"] = -branch_orginal["vdiff_min"]
                else
                        push!(orientations, orientation)
                end

        end


    for (i,branch) in ref(pm, n, :branch)
                bp = (branch["f_bus"], branch["t_bus"])
                tm = branch["tap"]
                b_fr = branch["b_fr"]
                g, b = PowerModels.calc_branch_y(branch)
                p    = var(pm, n, c, :p)
                q    = var(pm, n, c, :q)
                p_fr = p[(i,branch["f_bus"],branch["t_bus"])]
                q_fr = q[(i,branch["f_bus"],branch["t_bus"])]
                p_to = p[(i,branch["t_bus"],branch["f_bus"])]
                q_to = q[(i,branch["t_bus"],branch["f_bus"])]
                w_fr = w[branch["f_bus"]]
                w_to = w[branch["t_bus"]]
                vvv_fr = var(pm, n, c, :vvv_fr, (branch["f_bus"], branch["t_bus"]))
                vvv_to = var(pm, n, c, :vvv_to, (branch["f_bus"], branch["t_bus"]))

      @constraint(pm.model,  vvv_fr + vvv_to == (1/(g^2+b^2+b*b_fr))*(g*(p_fr-p_to)-b*(q_fr-q_to)))
    end

    for (i,branch) in ref(pm, n, :branch)
        pair = (branch["f_bus"], branch["t_bus"])
        buspair = ref(pm, n, :buspairs, pair)

        #vdiff_max = buspair["vdiff_max"]
        #vdiff_min = buspair["vdiff_min"]
        vdiff_max = branch["vdiff_max"]
        vdiff_min = branch["vdiff_min"]
        vm_fr = var(pm, n, c, :vm, branch["f_bus"])
        vm_to = var(pm, n, c, :vm, branch["t_bus"])

        @constraint(pm.model, vm_fr - vm_to <= vdiff_max)
        @constraint(pm.model, vm_fr - vm_to >= vdiff_min)

        vv = var(pm, n, c, :vv, (branch["f_bus"], branch["t_bus"]))
        vd = var(pm, n, c, :vd, (branch["f_bus"], branch["t_bus"]))
        vd_squared = var(pm, n, c, :vd_squared, (branch["f_bus"], branch["t_bus"]))
        w_fr = var(pm, n, c, :w, branch["f_bus"])
        w_to = var(pm, n, c, :w, branch["t_bus"])

        @constraint(pm.model, vv == (w_fr + w_to - vd_squared)/2)
        @constraint(pm.model, vd_squared <= w_fr - 2*vv + w_to)

        alpha_fr = branch["alpha_fr"]
        beta_fr = branch["beta_fr"]
        @constraint(pm.model, vm_to - alpha_fr*vm_fr <= beta_fr)
        @constraint(pm.model, vm_to - alpha_fr*vm_fr >= -beta_fr)
        @constraint(pm.model,   w_to - 2*alpha_fr*vv + alpha_fr^2 *w_fr <= beta_fr^2)
        @constraint(pm.model,   w_to + 2*alpha_fr*vv + alpha_fr^2 * w_fr <= 4*alpha_fr*vv + beta_fr^2)

        # to prevent this constraint from being posted on multiple parallel branchs
        if buspair["branch"] == i
            PMs.constraint_power_magnitude_sqr(pm, i, nw=n, cnd=c)
            PMs.constraint_power_magnitude_link(pm, i, nw=n, cnd=c)
        end
    end

end

#function constraint_voltage_magnitude_difference_neghboring_buses(pm::GenericPowerModel{T}, n::Int, c::Int, f_bus, t_bus, vdiff_min, vdiff_max) where T <: QCWRForm
#    vm_fr = var(pm, n, c, :vm, f_bus)
#    vm_to = var(pm, n, c, :vm, t_bus)

#    @constraint(pm.model, vm_fr - vm_to <= vdiff_max)
#    @constraint(pm.model, vm_fr - vm_to >= vdiff_min)
#end

#function constraint_voltage_magnitude_diff_sqr_equality{T <: QCWRTriVForm}(pm::GenericPowerModel{T}, n::Int, c::Int, f_bus, t_bus)
#    w_fr = var(pm, n, c, :w, f_bus)
#    w_to = var(pm, n, c, :w, t_bus)
#    vv = var(pm, n, c, :vv, (f_bus, t_bus))
#    vd = var(pm, n, c, :vd, (f_bus, t_bus))
#
#    @constraint(pm.model, vv == (w_fr + w_to - vd_squared)/2)
#end

#function constraint_voltage_magnitude_diff_sqr_inequality{T <: QCWRTriVForm}(pm::GenericPowerModel{T}, n::Int, c::Int, f_bus, t_bus)
#    w_fr = var(pm, n, c, :w, f_bus)
#    w_to = var(pm, n, c, :w, t_bus)
#    vv = var(pm, n, c, :vv, (f_bus, t_bus))
#    vd = var(pm, n, c, :vd, (f_bus, t_bus))
#
#    @constraint(pm.model, vd_squared <= w_fr - 2*vv + w_to)

#end

#function constraint_voltage_magnitude_diff_link{T <: QCWRTriVForm}(pm::GenericPowerModel{T}, n::Int, c::Int, f_idx, t_idx, f_bus, t_bus, g, b, b_fr)
#    p_fr = var(pm, n, c, :p, arcs_from)
#    q_fr = var(pm, n, c, :q, arcs_from)
#    q_to = var(pm, n, c, :q, arcs_to)
#    p_to = var(pm, n, c, :p, arcs_to)
#    vd = var(pm, n, c, :vd, (f_bus, t_bus))
#    vvv_fr = var(pm, n, c, :vvv_fr, f_bus)
#    vvv_to = var(pm, n, c, :vvv_to, t_bus)
#
#    @constraint(pm.model,  vvv_fr + vvv_to == (1/(g^2+b^2+b*b_fr))*(g*(p_fr-p_to)-b*(q_fr-q_to)))

#end


# Following constraints are Dmitry's constraints in the ShareLatex file

#function constraint_voltage_magnitude_diff_dim1{T <: QCWRTriVForm}(pm::GenericPowerModel{T}, n::Int, c::Int, f_bus, t_bus, alpha_fr, beta_fr)
#    vm_fr = var(pm, n, c, :vm, f_bus)
#    vm_to = var(pm, n, c, :vm, t_bus)

#    @constraint(pm.model, vm_to - alpha_fr*vm_fr <= beta_fr)
#    @constraint(pm.model, vm_to - alpha_fr*vm_fr >= -beta_fr)
#end

#function constraint_voltage_magnitude_diff_dim2{T <: QCWRTriVForm}(pm::GenericPowerModel{T}, n::Int, c::Int, f_bus, t_bus, alpha_fr, beta_fr)
#    vm_fr = var(pm, n, c, :vm, f_bus)
#    vm_to = var(pm, n, c, :vm, t_bus)
#    w_fr = var(pm, n, c, :w, f_bus)
#    w_to = var(pm, n, c, :w, t_bus)
#    vv = var(pm, n, c, :vv, (f_bus, t_bus))

#    @constraint(pm.model,   w_to - 2*alpha_fr*vv + alpha_fr^2 *w_fr <= beta_fr^2)

#end

#function constraint_voltage_magnitude_diff_dim3{T <: QCWRTriVForm}(pm::GenericPowerModel{T}, n::Int, c::Int, f_bus, t_bus, alpha_fr, beta_fr)
#    vm_fr = var(pm, n, c, :vm, f_bus)
#    vm_to = var(pm, n, c, :vm, t_bus)
#    vv = var(pm, n, c, :vv, (f_bus, t_bus))
#
#    @constraint(pm.model,  w_to + 2*alpha_fr*vv + alpha_fr^2 * w_fr <= 4*alpha_fr*vv + beta_fr^2)

#end
