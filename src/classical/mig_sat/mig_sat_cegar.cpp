/* CirKit: A circuit toolkit
 * Copyright (C) 2009-2015  University of Bremen
 * Copyright (C) 2015-2016  EPFL
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "mig_sat_cegar.hpp"

#include <iostream>
#include <cmath>
#include <memory>
#include <ctime>

#include <boost/dynamic_bitset.hpp>
#include <boost/format.hpp>
#include <boost/optional.hpp>

#include <classical/abc/abc_api.hpp>
#include <classical/abc/abc_manager.hpp>
#include <classical/sat/operations/cardinality.hpp>
#include <classical/sat/abcsat.hpp>

#include <core/utils/range_utils.hpp>
#include <core/utils/timer.hpp>
#include <core/utils/timeout.hpp>
#include <classical/mig_sat/spec_representation_mign.hpp>

#include <classical/mign/mign.hpp>
#include <classical/mign/mign_utils.hpp>
#include <classical/mign/mign_simulate.hpp>
#include <classical/mign/mign_invfree.hpp>

#include "sat/bsat/satSolver.h"

using namespace boost::assign;

using boost::format;
using boost::str;

namespace abc
{

sat_solver* sat_solver_new(); 
void sat_solver_setnvars(sat_solver* s,int n);
int Abc_Var2Lit( int x, int c );
void sat_solver_addclause( sat_solver* solver, int a, int b);
int sat_solver_solve(sat_solver* s, lit* begin, lit* end, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, ABC_INT64_T nConfLimitGlobal, ABC_INT64_T nInsLimitGlobal);
int sat_solver_var_value( sat_solver* solver, int i );
}

namespace cirkit
{

std::vector<tt> tt_simulate_MO( mign_graph mign)
{
	std::vector<tt> tt_func;
	const mign_tt_simulator simulator{};
	auto values = simulate_mign(mign, simulator);
	tt_func.resize(mign.outputs().size());
	auto one_output = mign.outputs(); 
	for ( auto x = 0u; x < tt_func.size(); x++)
	{
		tt_func[x] = values[one_output[x].first];
		tt_func[x].resize(pow(2,mign.inputs().size())); 
	}
	return tt_func; 
}

int check_fo (mign_graph& mign, int fanout)
{
	mign.compute_fanout(); 
	for (auto& node :mign.topological_nodes())
	{
		if (mign.is_input(node))
			continue; 
		if (node == 0)
			continue; 
		if (mign.fanout_count(node) <= fanout)
			continue; 
		else 
			return node - mign.inputs().size() - 1; 
	}
	return -1; 
}
	
struct exact_inst_cegar
{
	
exact_inst_cegar( unsigned num_vars, bool verbose, unsigned n_output) :
      SpecVars ( num_vars ), 
	  eVerbose (verbose), 
	  SpecFunc (n_output)
    {
		Sat = NULL; 
		Rows = pow(2,SpecVars) - 1; // -1 eliminating the 000 normal 
    }
	
	
void tt_from_spec_MO( mign_graph mign, std::vector<bool> normal_MO)
{
	const mign_tt_simulator simulator{};
	auto values = simulate_mign(mign, simulator);
	tt_Spec.resize(mign.outputs().size());
	tt_Spec_orig.resize(mign.outputs().size());
	auto one_output = mign.outputs(); 
	for ( auto x = 0u; x < tt_Spec.size(); x++)
	{
		tt_Spec_orig[x] = values[one_output[x].first];
		tt_Spec[x] = values[one_output[x].first];
		tt_Spec[x].resize(pow(2,SpecVars));
		tt_Spec_orig[x].resize(pow(2,SpecVars));
		if (normal_MO[x] == 0)
		{
			tt_Spec[x].flip(); 
		}
	}
}


bool check (std::vector<tt> func)
{
	assert (tt_Spec_orig.size() == func.size());
	for ( auto x = 0u; x < tt_Spec_orig.size(); x++)
	{
		if (tt_Spec_orig[x] == func[x])
			continue; 
		else 
			return false; 
	}
	return true; 
}

std::vector<std::pair<unsigned, unsigned>> tt_symmetric (tt spec)
{
    std::vector<std::pair<unsigned, unsigned>> symm_pairs;

    const auto n = tt_num_vars( spec );

    for ( auto j = 1u; j < n; ++j )
    {
      for ( auto i = 0u; i < j; ++i )
      {
        if ( tt_permute( spec, i, j ) == spec )
        {
          symm_pairs.push_back( {i, j} );
        }
      }
    }
	
	return symm_pairs; 
}

void create_var (int ngate, int depth, int fanout)
{
	Noper = 16; 
    nGates      = ngate; // r 
    nSimVars    = nGates * Rows; // xit
	nOutputVars = SpecFunc * nGates; 
    nGateVars   = nGates * 7; // 7 combinations with 3 inputs
    nSelectVars = 0;
    for ( auto i = SpecVars; i < SpecVars + nGates; i++ )
          nSelectVars += ( i * ( i - 1 ) * (i - 2) ) / 6; 
	nOutputOffset = nSimVars;
	nGateOffset   = nSimVars + nOutputVars;
	nSelectOffset = nSimVars + nOutputVars + nGateVars;
	   
    abc_manager::get();
    abc::Abc_FrameGetGlobalFrame();
	
     /* if we already have a SAT solver, then restart it (this saves a lot of time) */
	
    if ( Sat )
	   abc::sat_solver_restart( Sat );
    else
       Sat = abc::sat_solver_new();
	
	nOperVars = Noper * nGates; // to allow only majorities operations 
	nOperOffset = nSimVars + nOutputVars + nGateVars + nSelectVars; 
	
	MaxDepth = depth; 
	MaxFanout = fanout; 
	nDepthVars = MaxDepth > 0 ? ( nGates * ( nGates + 1 ) ) / 2 : 0;
	nDepthOffset = nSimVars + nOutputVars + nGateVars + nSelectVars + nOperOffset; 
	
    abc::sat_solver_setnvars( Sat, nSimVars + nOutputVars + nGateVars + nSelectVars + nOperVars + nDepthVars);

}

int SimVar( int i, int t )
{
	// no Offset for SImVar
    assert( i < nGates );
    assert( t < Rows );

    return Rows * i + t;
}

int GateVar( int i, int p, int q, int u )
{
    assert( i < nGates );
    assert( p < 2 );
    assert( q < 2 );
	assert( u < 2); 
    assert( p > 0 || q > 0 || u > 0); 

    return nGateOffset + i * 7 + ( p << 1 ) + 2*p + (q << 1) + u - 1;
}

int SelectVar( int i, int j, int k, int w )
{
    int a;
    int offset;

    assert( i < nGates );
    assert( w < SpecVars + i );
    assert( j < k );
	assert( k < w );

    offset = nSelectOffset;
    for ( a = SpecVars; a < SpecVars + i; ++a ) 
	    offset += a * (a-1) * (a-2) / 6; 
	for (auto x = 0; x < j; x++)
	{
		offset = offset + ((SpecVars  + i -1 - x) * (SpecVars + i - 2 - x))/2;
	}

    return offset + ( -(k-j-1) * (  k -j- 2 * ( SpecVars - 1 + i -j ) ) ) / 2 + ( w - k - 1 ) ;
}

int OutputVar(  int h, int i )
{
    assert( h < SpecFunc );
    assert( i < nGates );

    return nOutputOffset + nGates * h + i;
}

int OperVar( int i, int g)
{
    assert( i < Noper);
    return nOperOffset +  i + g * Noper;
}

int DepthVar (int i, int l)  // dil
{
	assert( l >= 0 );
	assert( i < nGates );
    assert( l <= i );

	return nDepthOffset + ( ( i * ( i + 1 ) ) / 2 ) + l ;   
}

void create_main_clauses (int t, int i, int j, int k, int w, int a, int b, int c, int d) 
{
	
	int pLits[6], ctr = 0;

	pLits[ctr++] = abc::Abc_Var2Lit( SelectVar( i, j, k, w ), 1 ); 
    pLits[ctr++] = abc::Abc_Var2Lit( SimVar( i, t ), a );

	if ( j < SpecVars ) // if j <= n xjt is constant because they are pointing to PI
	    {
	        if ( ( ( ( t + 1 ) & ( 1 << j ) ) ? 1 : 0 ) != b )
	            return;
	    }
	else
	    pLits[ctr++] = abc::Abc_Var2Lit( SimVar(j - SpecVars, t ), b );

	if ( k < SpecVars ) // if k <= n xkt is constant 
	    {
	        if ( ( ( ( t + 1 ) & ( 1 << k ) ) ? 1 : 0 ) != c )
	            return;
	    }
	else
	    pLits[ctr++] = abc::Abc_Var2Lit( SimVar( k - SpecVars, t ), c );
	
	if ( w < SpecVars ) // if k <= n xkt is constant 
	    {
	        if ( ( ( ( t + 1 ) & ( 1 << w ) ) ? 1 : 0 ) != d )
	            return;
	    }
	else
	    pLits[ctr++] = abc::Abc_Var2Lit( SimVar( w - SpecVars, t ), d );
 
    if ( b > 0 || c > 0 || d > 0 ) // otherwise omitting the last term. Because 0 <=> 0 is 1, and 1 V something always = 1. 
	   {
	   	 pLits[ctr++] = abc::Abc_Var2Lit( GateVar(i, b, c , d), 1 - a );
	   }
	
	abc::sat_solver_addclause(Sat , pLits, pLits + ctr );
}

int Depthclause ()
{
    int i, j, k, w, l, d, h, jj, kk, ww;
    int pLits[3];

    for ( i = 0; i < nGates; ++i )
    {
        /* propagate depths from children */ 
		for ( w = 2; w < i; w++)   
		     for ( k = 1; k < w; ++k )
		            for ( j = 0; j < k; ++j )
		            {
		                pLits[0] = abc::Abc_Var2Lit( SelectVar( i, SpecVars + j, SpecVars + k , SpecVars + w), 1 );
		                for ( jj = 0; jj <= j; ++jj )
		                {
							
		                    pLits[1] = abc::Abc_Var2Lit( DepthVar( j, jj ), 1 );
		                    pLits[2] = abc::Abc_Var2Lit( DepthVar( i, jj + 1 ), 0 );
		                    abc::sat_solver_addclause( Sat, pLits, pLits + 3 );
		                }
		            }
		
		for ( w = 1; w < i; ++w)
		     for ( k = 0; k < w; ++k ) // for k ==. to be done only if k > n
			      for ( j = 0; j < SpecVars + k; ++j )
					   {
					     pLits[0] = abc::Abc_Var2Lit( SelectVar( i, j, SpecVars + k, SpecVars + w ), 1 );
					     for ( kk = 0; kk <= k; ++kk )
					      {
					         pLits[1] = abc::Abc_Var2Lit( DepthVar( k, kk ), 1 );
					         pLits[2] = abc::Abc_Var2Lit( DepthVar( i, kk + 1 ), 0 );
					         abc::sat_solver_addclause( Sat, pLits, pLits + 3 );
					       }
					    }
					
		for ( w = 0u; w < i; ++w)
			for ( k = 0; k < SpecVars + w; ++k ) // for w ==. to be done only if k > n
				for ( j = 0; j < k; ++j )
					{
					pLits[0] = abc::Abc_Var2Lit( SelectVar( i, j, k, SpecVars + w ), 1 );
					for ( ww = 0; ww <= w; ++ww )
					  {
						pLits[1] = abc::Abc_Var2Lit( DepthVar( w, ww ), 1 );
						pLits[2] = abc::Abc_Var2Lit( DepthVar( i, ww + 1 ), 0 );
						abc::sat_solver_addclause( Sat, pLits, pLits + 3 );
					  }
				    }
      
         /* arrival times are 0 for inputs */
         pLits[0] = abc::Abc_Var2Lit( DepthVar( i, 0 ), 0 );
         abc::sat_solver_addclause( Sat, pLits, pLits + 1 );
        
        /* reverse order encoding of depth variables */
        for ( j = 1; j <= i; ++j )
        {
            pLits[0] = abc::Abc_Var2Lit( DepthVar(  i, j ), 1 );
            pLits[1] = abc::Abc_Var2Lit( DepthVar( i, j - 1 ), 0 );
            abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
        }

        /* constrain maximum depth */
        if ( MaxDepth <= i )
            for ( h = 0; h < SpecFunc; ++h )
            {
                pLits[0] = abc::Abc_Var2Lit( OutputVar( h, i ), 1 );
                pLits[1] = abc::Abc_Var2Lit( DepthVar( i, MaxDepth ), 1 );
                if ( !abc::sat_solver_addclause(Sat, pLits, pLits + 2 ) )
                    return 0;
            } 
    }

    return 1;
}

int add_fanout (mign_node node)
{

	int i, k, j, w, ii, h; 
	auto settings = std::make_shared<properties>(); 
	settings-> set("reuse_solver", Sat); 
	auto solver = make_solver<abc_solver>(settings); 
	std::vector<int> pLits; 

	i = node; 
	for ( ii = i + 1; ii <nGates; ii++)
        for ( j = 0; j < ii + SpecVars; j++)
			for ( k = j + 1; k < ii + SpecVars; k++)
				for ( w = k + 1; w < ii + SpecVars; w++)
	{
		if ((j == i + SpecVars) || (k == i + SpecVars) || (w == i + SpecVars))
		{
			pLits.push_back(SelectVar( ii,  j, k ,  w) + 1);
		}
	}
	
    for ( h = 0; h < SpecFunc; ++h )
    {
		pLits.push_back(OutputVar( h, i ) + 1); 	
	}

	if (pLits.size() > 1)
	less_or_equal_bailleux_boufkhad( solver, pLits, MaxFanout, sat_solver_nvars( Sat ) + 1 );

    return 1;
}


int create_tt_clauses( int t )
{
    int i, j, k, h, w;
    int pLits[2];

    for ( i = 0; i < nGates; ++i )
    {
        /* main clauses */
        for ( j = 0; j < SpecVars + i; ++j )
            for ( k = j + 1; k < SpecVars + i; ++k )
				for ( w = k + 1; w < SpecVars + i; ++w)
            {
                create_main_clauses(  t, i, j, k, w,  0, 0, 0, 1 );
				create_main_clauses(  t, i, j, k, w,  0, 0, 1, 0 );
				create_main_clauses(  t, i, j, k, w,  0, 0, 1, 1 );
				create_main_clauses(  t, i, j, k, w,  0, 1, 0, 0 );
				create_main_clauses(  t, i, j, k, w,  0, 1, 0, 1 );
				create_main_clauses(  t, i, j, k, w,  0, 1, 1, 0 );
				create_main_clauses(  t, i, j, k, w,  0, 1, 1, 1 );
                create_main_clauses(  t, i, j, k, w,  1, 0, 0, 1 );
				create_main_clauses(  t, i, j, k, w,  1, 0, 0, 0 ); 
				create_main_clauses(  t, i, j, k, w,  1, 0, 1, 0 );
				create_main_clauses(  t, i, j, k, w,  1, 0, 1, 1 );
				create_main_clauses(  t, i, j, k, w,  1, 1, 0, 0 );
				create_main_clauses(  t, i, j, k, w,  1, 1, 0, 1 );
				create_main_clauses(  t, i, j, k, w,  1, 1, 1, 0 );
				create_main_clauses(  t, i, j, k, w,  1, 1, 1, 1 );
            }

            for ( h = 0; h < SpecFunc; ++h )
            {
                pLits[0] = abc::Abc_Var2Lit( OutputVar(  h, i ), 1 ); //complemented !ghi
                pLits[1] = abc::Abc_Var2Lit( SimVar( i, t ), 1 - tt_Spec[h][t + 1] ); 
				
                if ( !abc::sat_solver_addclause( Sat, pLits, pLits + 2 ) )
                    return 0;
            }
    }
	
    return 1;
}

int add_more_clauses(std::vector<tt> tt_mign_new)
{
	int t = -1; 
	
	for (auto x = 0u; x < tt_Spec_orig.size(); x++)
	{
			for (auto y = 1u; y <tt_mign_new[x].size(); y++)
			{
				if (tt_Spec_orig[x][y] == tt_mign_new[x][y])
				{
					continue; 
				}
					
				else 
				{
					t = y;
				    x =  tt_Spec_orig.size(); 
					break; 
				}
			}
		}

	assert ( t > 0); 
	create_tt_clauses(t-1); 
	return 1; 
}

int create_clauses(unsigned option)
{
    int h, i, j, k, w, t, ii, jj, kk, ww, p, q, u;
    int pLits[2];
    int uLits[nGates]; 
	
	if ((option == 0) || (option == 2))
	{
	    for ( t = 0; t < Rows; ++t )
	    {
	            if ( !create_tt_clauses( t ) ) 
	               return 0;
	    }
	}
    
    /* if there is only one output, we know it must point to the last gate  */
    if ( SpecFunc == 1 )
    {
        for ( i = 0; i < nGates - 1; ++i )
        {
            pLits[0] = abc::Abc_Var2Lit( OutputVar( 0, i ), 1 );
            if ( !abc::sat_solver_addclause( Sat, pLits, pLits + 1 ) )
                return 0;
        }
        pLits[0] = abc::Abc_Var2Lit( OutputVar( 0, nGates - 1 ), 0 );
        if ( !abc::sat_solver_addclause( Sat, pLits, pLits + 1 ) )
            return 0;
    }
    else
    {
        /* some output is selected */
        for ( h = 0; h < SpecFunc; ++h )
        {
            for ( i = 0; i < nGates; ++i )
				uLits[i] = abc::Abc_Var2Lit( OutputVar( h, i ), 0 ); 	
			 abc::sat_solver_addclause( Sat, uLits, uLits + nGates );
        }
    }

    /* each gate has three operands */
    for ( i = 0; i < nGates; ++i )
    {
		int vLits[( ( SpecVars + i ) * ( SpecVars + i - 1 ) * ( SpecVars + i - 2)) / 6];
        jj = 0;
        for ( j = 0; j < SpecVars + i; ++j )
            for ( k = j + 1; k < SpecVars + i; ++k )
				for ( w = k + 1; w < SpecVars + i; ++w)
			    {
				vLits[jj++] = abc::Abc_Var2Lit( SelectVar(  i, j, k , w), 0 );  
				} 
        abc::sat_solver_addclause( Sat, vLits, vLits + jj );
    }
		
	if (MaxDepth > 0)
		Depthclause();  

     for ( i = 0; i < nGates; ++i )
        {// first maj operation <xyz> = M3
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 ); 
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(0,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
			// second maj operation <!xyz> = M3
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(1,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
			// second maj operation <x!yz> = M3
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(2,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
			// second maj operation <xy!z> = M4
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(3,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <0bc> = AND1
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(4,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <1bc> = AND1 neg 1
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(7,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				
				// second maj operation <0!bc> = AND1 neg 2
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(8,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				
				// second maj operation <0b!c> = AND1 neg 3
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(9,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <a0c> = AND2
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(5,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				
				// second maj operation <!a0c> = AND2 neg 1
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(10,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <a1c> = AND2 neg 2
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(11,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <a0!c> = AND2 neg 3
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(12,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <ab0> = AND3
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(6,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <!ab0> = AND3 neg 1
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(13,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <a!b0> = AND3 neg 2
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(14,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				// second maj operation <ab1> = AND3 neg 3
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 0, 1 ), 1 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 0, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 0, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );

            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 0 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
            	pLits[0] = abc::Abc_Var2Lit( GateVar( i, 1, 1, 1 ), 0 );
            	pLits[1] = abc::Abc_Var2Lit( OperVar(15,i), 1 );
            	abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
				
				//FINAL OR 
				int iLits[Noper]; 
				for ( auto f = 0; f < Noper; f++)
				{
					iLits[f] = abc::Abc_Var2Lit( OperVar(f,i), 0 );
				}
				
				abc::sat_solver_addclause( Sat, iLits, iLits + Noper ) ;
					
        }	
		

	    /* EXTRA clauses: use gate i at least once */
		std::vector<int> vLits; 

	    for ( i = 0; i < nGates; ++i )
	    {
	        jj = 0;
	        for ( h = 0; h < SpecFunc; ++h )
	            vLits.push_back(abc::Abc_Var2Lit( OutputVar(  h, i ), 0 )) ;
	        for ( ii = i + 1; ii < nGates; ++ii )
	        {
	            for ( j = 0; j < SpecVars + i; ++j )
					for (k = j + 1; k < SpecVars + i; k++)
				{
					vLits.push_back(abc::Abc_Var2Lit( SelectVar( ii, j, k, SpecVars + i), 0 )) ;
				}
	                      
	            for ( k = SpecVars + i + 1; k < SpecVars + ii; k++ )
					 for ( w = k + 1; w < SpecVars + ii; w++ )
				{
					  vLits.push_back(abc::Abc_Var2Lit( SelectVar( ii, SpecVars + i, k , w ), 0 )) ;
				}
	                   
	            for ( j = 0; j < SpecVars + i; j++ )
					for (w = SpecVars + i + 1; w < SpecVars + ii; w++)
				{
					vLits.push_back(abc::Abc_Var2Lit( SelectVar( ii, j, SpecVars + i, w ), 0 )) ;  
				}
	                     
	        }
			int array[vLits.size()]; 
			std::copy(vLits.begin(), vLits.end(), array);
            abc::sat_solver_addclause( Sat, array , array + vLits.size());
	    }

	    /* EXTRA clauses: co-lexicographic order */
	    for ( i = 0; i < nGates - 1; ++i )
	    {
			for ( w = 3; w < SpecVars + i; w++)
			{
				for ( k = 2; k < w; k++)
				{
					for (j = 1; j < k; j++)
						for ( jj = 0; jj < j; ++jj)
					{
						
	                    pLits[0] = abc::Abc_Var2Lit( SelectVar( i, j, k, w ), 1 );
	                    pLits[1] = abc::Abc_Var2Lit( SelectVar( i + 1, jj, k , w), 1 );
						abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
					}
				}
				
				
				for ( k = 1; k < w; k++)
				{
		            for ( j = 0; j < k; ++j )
		                for ( kk = 1; kk < k; ++kk )
		                    for ( jj = 0; jj < kk; ++jj )
		                    {
								//std::cout << " caso 2" << std::endl;
		                        pLits[0] = abc::Abc_Var2Lit( SelectVar( i, j, k, w ), 1 );
		                        pLits[1] = abc::Abc_Var2Lit( SelectVar( i + 1, jj, kk , w), 1 );
								abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
		                    }
				}
				
				for ( k = 1; k < w; k++)
				{
		            for ( j = 0; j < k; ++j )
						for ( ww = 1; ww < w; ++ww)
		                    for ( kk = 1; kk < ww; ++kk )
		                         for ( jj = 0; jj < kk; ++jj )
		                         {
		                             pLits[0] = abc::Abc_Var2Lit( SelectVar(  i, j, k, w ), 1 );
		                             pLits[1] = abc::Abc_Var2Lit( SelectVar( i + 1, jj, kk , ww), 1 );
									 abc::sat_solver_addclause( Sat, pLits, pLits + 2 );
		                         }
				}
				
			}
	           
	    }
	    
	    /* EXTRA clauses: symmetric variables */
	    if ( SpecFunc == 1 ) 
	    {
			auto pairs = tt_symmetric (tt_Spec[0]); 
			std::vector<int> hLits; 
		    for ( auto& pa : pairs)
		    {
		         p = pa.first; 
		         q = pa.second; 
		
	             if ( eVerbose )
	             printf( "variables %d and %d are symmetric\n", p, q );
	             for ( i = 0; i < nGates; ++i )
					 for ( k = 1; k < q; ++k)
	                     for ( j = 0; j < k; ++j )
	                     {
	                        if (( j == p ) || (k == p)) continue;
							hLits.push_back(abc::Abc_Var2Lit( SelectVar( i, j, k, q ), 1 ) );
	                        for ( ii = 0; ii < i; ++ii )
								for ( ww = 2; ww < SpecVars + ii; ++ww)
	                                 for ( kk = 1; kk < ww; ++kk )
	                                    for ( jj = 0; jj < kk; ++jj )
	                                        if ( jj == p || kk == p || ww == p )
							{
								hLits.push_back(abc::Abc_Var2Lit( SelectVar( ii, jj, kk, ww ), 0 ) );
							}
							int array[hLits.size()]; 
							std::copy(hLits.begin(), hLits.end(), array);
	                        abc::sat_solver_addclause( Sat, array , array + hLits.size());

	                        }
	                }
				}
    return 1;
}

int Sat_Solve()
{
    int status;
    abc::abctime timeStart, timeDelta;

    timeStart = abc::Abc_Clock();
    status = sat_solver_solve( Sat, NULL, NULL, nBTLimit, 0, 0, 0 );
    timeDelta = abc::Abc_Clock() - timeStart;

	timeSat += timeDelta;

    if ( status == abc::l_True )
    {
        nSatCalls++;
        timeSatSat += timeDelta;
        return 1;
    }
    else if ( status == abc::l_False )
    {
        nUnsatCalls++;
        timeSatUnsat += timeDelta;
        return 0;
    }
    else
    {
        nUndefCalls++;
        timeSatUndef += timeDelta;
        if ( eVerbose )
        {
            printf( "resource limit reached\n" );
        }
        return 2;
    }
}  

void print_debug()
{
	int i, h, j, k , w, nOp, g; 
	
	 for ( i = 0; i < nGates; ++i )
	 {
		 std::cout << " GATE " << i + SpecVars << std::endl; 
		 
 		for (auto t = 0; t < Rows; t++)
			std::cout << SimVar(i,t) << "  " << "x(" << i << "," << t <<  ")" << " = " << abc::sat_solver_var_value(Sat, SimVar(i,t) ) << std::endl;
		
		for ( h = 0; h < SpecFunc; h++)
			std::cout << OutputVar(h,i) << "  " << "g(" << h << "," << i <<  ")" << " = " << abc::sat_solver_var_value(Sat, OutputVar(h,i) ) << std::endl;
		
		std::cout << GateVar(i, 0, 0, 1) << "  " << "f(" << i << "," << 0 << "," << 0 << "," << 1 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,0,0,1) ) << std::endl;
		std::cout << GateVar(i, 0, 1, 0) << "  " << "f(" << i << "," << 0 << "," << 1 << "," << 0 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,0,1,0) ) << std::endl;
		std::cout << GateVar(i, 0, 1, 1) << "  " << "f(" << i << "," << 0 << "," << 1 << "," << 1 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,0,1,1) ) << std::endl;
		std::cout << GateVar(i, 1, 0, 0) << "  " << "f(" << i << "," << 1 << "," << 0 << "," << 0 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,1,0,0) ) << std::endl;
		std::cout << GateVar(i, 1, 0, 1) << "  " << "f(" << i << "," << 1 << "," << 0 << "," << 1 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,1,0,1) ) << std::endl;
		std::cout << GateVar(i, 1, 1, 0) << "  " << "f(" << i << "," << 1 << "," << 1 << "," << 0 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,1,1,0) ) << std::endl;
		std::cout << GateVar(i, 1, 1, 1) << "  " << "f(" << i << "," << 1 << "," << 1 << "," << 1 << ")" << " = " << abc::sat_solver_var_value(Sat, GateVar(i,1,1,1) ) << std::endl;
		
		 
	 	for ( w = 0; w < SpecVars + i; ++w)
	         for ( k = 0; k < w; ++k )
	              for ( j = 0; j < k; ++j )
						 {
							 std::cout << SelectVar(i, j, k, w) << "  " << "s(" << i << "," << j << "," << k << "," << w << ")" << " = " << abc::sat_solver_var_value(Sat, SelectVar(i, j, k, w) ) << std::endl;
							
						 }
		
		
	 for ( auto x = 0u; x < 16; x++)
		 {
			 std::cout << OperVar(x,i) << "  " << "op(" << x << "," << i << ")" << " = " << abc::sat_solver_var_value(Sat, OperVar(x,i ) ) << std::endl; 
		 }
		 
		 if (MaxDepth > 0)
		{ 
			for (auto l = 0; l <=i ; l++)
		 {
			 std::cout << DepthVar(i,l) << "  " << "d(" << i << "," << l << ")" << " = " << abc::sat_solver_var_value(Sat, DepthVar(i,l ) ) << std::endl; 
		 } 
	 }
	
	 }
}


std::vector<mign_graph> extract_mig_MO( std::string model_name, std::vector<bool> normal_ori, bool verbose)
{
	std::vector<mign_graph> mign; 
    int nSol, h, i, j, k, nOp, w;
	
	mign.resize(1); // for now only one possible solution ;) 
	
	mign[0].set_name(model_name);
	//mign[0].structural_hashing(1) ;   // disable structural hashing 
	
	std::unordered_map<mign_node, mign_function> node_to_function;
	// INPUTS 
	mign[0].get_constant(false);
	mign[0].get_constant(true);
	
	for ( auto inputs = 0; inputs < SpecVars; ++inputs)
	{
		auto name = boost::str( boost::format( "x_%d" ) % inputs);
		node_to_function.insert ({inputs, mign[0].create_pi(name)}); 
	}

    /* gates */
    for ( i = 0; i < nGates; ++i )
    {
		auto flag = 0; 
		std::vector<bool> compl_input (3); 
		if (abc::sat_solver_var_value(Sat, OperVar(0,i ) ))
		{
			flag = 1; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(1,i ) ))
		{
			flag = 1; 
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(2,i ) ))
		{
			flag = 1; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(3,i ) ))
		{
			flag = 1; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(4,i ) ))  // AND 0bc
		{
			flag = 2; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(7,i ) ))
		{
			flag = 2;
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(8,i ) ))
		{
			flag = 2; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(9,i ) ))
		{
			flag = 2; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(5,i ) ))  // AND a0c
		{
			flag = 3; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(10,i ) ))
		{
			flag = 3;
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(11,i ) ))
		{
			flag = 3; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(12,i ) ))
		{
			flag = 3; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(6,i ) ))  // AND ab0
		{
			flag = 4; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(13,i ) ))
		{
			flag = 4;
			compl_input[0] = 1; 
			compl_input[1] = 0; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(14,i ) ))
		{
			flag = 4; 
			compl_input[0] = 0; 
			compl_input[1] = 1; 
			compl_input[2] = 0; 
		}
		else if (abc::sat_solver_var_value(Sat, OperVar(15,i ) ))
		{
			flag = 4; 
			compl_input[0] = 0; 
			compl_input[1] = 0; 
			compl_input[2] = 1; 
		} 
	
        nOp  = abc::sat_solver_var_value(Sat, GateVar( i, 0, 0, 1 ) );

       
		for ( w = 0; w < SpecVars + i; ++w)
            for ( k = 0; k < w; ++k )
                for ( j = 0; j < k; ++j )
                     if ( sat_solver_var_value( Sat, SelectVar( i, j, k, w ) ) )
                     {
                       // printf( " and operands %d and %d and %d", j, k, w );
						std::vector<mign_function> operands;
						if (flag == 1)
						{
							operands.push_back(node_to_function.at(j)^compl_input[0]); 
							operands.push_back(node_to_function.at(k)^compl_input[1]); 
							operands.push_back(node_to_function.at(w)^compl_input[2]); 
							node_to_function.insert({SpecVars + i, mign[0].create_maj(operands)});
						}
						
						else if ( flag == 2)
						{
							operands.push_back(node_to_function.at(k)^compl_input[1]); 
							operands.push_back(node_to_function.at(w)^compl_input[2]);
							if (compl_input[0] == 1)
							{
								node_to_function.insert({SpecVars + i, mign[0].create_or(operands)});
							}
							else 
								node_to_function.insert({SpecVars + i, mign[0].create_and(operands)});
						}
						else if ( flag == 3)
						{
							operands.push_back(node_to_function.at(j)^compl_input[0]); 
							operands.push_back(node_to_function.at(w)^compl_input[2]);
							if (compl_input[1] == 1)
							{
								node_to_function.insert({SpecVars + i, mign[0].create_or(operands)});
							}
							else 
								node_to_function.insert({SpecVars + i, mign[0].create_and(operands)});
						}
						else if ( flag == 4)
						{
							operands.push_back(node_to_function.at(j)^compl_input[0]); 
							operands.push_back(node_to_function.at(k)^compl_input[1]);
							if (compl_input[2] == 1)
							{
								node_to_function.insert({SpecVars + i, mign[0].create_or(operands)});
							}
							else 
								node_to_function.insert({SpecVars + i, mign[0].create_and(operands)});
						}
						 
                        w = SpecVars + i;  // E qui che sto considerando una sola soluzione possibile?? 
						k = w; 
                        break;
                      }
    }
		

    /* outputs */
    for ( h = 0; h < SpecFunc; ++h )
        for ( i = 0; i < nGates; ++i )
	   {
		if ( sat_solver_var_value( Sat, OutputVar( h, i ) ) )
            {
					auto output_name = str( format( "f_%d" ) % h ); 
					if (!normal_ori[h])
						mign[0].create_po (create_mign_function(node_to_function.at(SpecVars + i).node, 1), output_name); 
					else 
						mign[0].create_po (create_mign_function(node_to_function.at(SpecVars + i).node, 0), output_name);
					i = nGates; 
				break; 	
            }
		}
			return mign; 
}


		abc::sat_solver * Sat;              /* SAT solver */
		bool  eVerbose; 
        std::vector<tt> tt_Spec;            /* specification */
		std::vector<tt> tt_Spec_orig;       /* specification not changed by normal*/
        int          SpecVars;              /* number of variables in specification = n */
		int          SpecFunc;              /* number of functions to synthesize = m */
        int          Rows;                  /* number of rows in the specification (without 0) */
        int          MaxDepth;              /* maximum depth  */
		int          MaxFanout;             /* maximum depth  */

        int          nBTLimit = 0;          /* conflict limit */
      

		int          Noper ;                /* Number of operation allowed */
        int          nGates;                /* number of gates */
        int          nStartGates;           /* number of gates to start search (-1), i.e., to start from 1 gate, one needs to specify 0 */
        int          nMaxGates;             /* maximum number of gates given max. delay and arrival times */
        int          fDecStructure;         /* set to 1 or higher if SpecFunc = 1 and f = x_i OP g(X \ {x_i}), otherwise 0 (determined when solving) */
       
        int          nSimVars;              /* number of simulation vars x(i, t) */
        int          nOutputVars;           /* number of output variables g(h, i) */
        int          nGateVars;             /* number of gate variables f(i, p, q) */
        int          nSelectVars;           /* number of select variables s(i, j, k) */
        int          nOperVars;             /* number of operations variables op_i */
		int          nDepthVars;            /* number of depth variables d(i,j) */
		
        int          nOutputOffset;         /* offset where output variables start */
        int          nGateOffset;           /* offset where gate variables start */
        int          nSelectOffset;         /* offset where select variables start */
		int          nOperOffset;           /* offset where possible operations start */
		int          nDepthOffset;          /* offset where depth variables start */
		
        int          fHitResLimit;          /* SAT solver gave up due to resource limit */
		
	    abc::abctime      timeSat;          /* SAT runtime */
	    abc::abctime      timeSatSat;       /* SAT runtime (sat instance) */
	    abc::abctime      timeSatUnsat;     /* SAT runtime (unsat instance) */
	    abc::abctime      timeSatUndef;     /* SAT runtime (undef instance) */
	    abc::abctime      timeInstance;     /* creating instance runtime */
	    abc::abctime      timeTotal;        /* all runtime */
		
   
        int          nSatCalls;             /* number of SAT calls */
        int          nUnsatCalls;           /* number of UNSAT calls */
        int          nUndefCalls;           /* number of UNDEF calls */
    };

/******************************************************************************
* Private functions                                                          *
******************************************************************************/



class c_exact_mig_abc_manager_MO
{
public:
c_exact_mig_abc_manager_MO( const mign_graph& spec, unsigned cegar_option, int depth, int fanout, const properties::ptr& settings, const properties::ptr& statistics )
       : spec( spec ), 
         depth(depth), 
         fanout(fanout), 
         option(cegar_option)
{
       /* meta data */
	 model_name          = get( settings, "model_name",          std::string( "exact_sat_mign" ) );

	 start               = get( settings, "start",               spec.outputs().size() );
	
	 all_solutions       = get( settings, "all_solutions",       false );

       /* encoding */
      
	 timeout             = get( settings, "timeout",             boost::optional<unsigned>() );
     verbose             = get( settings, "verbose",             true );

}
	 
std::vector<mign_graph> run()
{
	std::vector<bool> normal_MO;
	
	for ( auto x = 0u; x < spec.outputs().size(); x++)
	{
	    const mign_tt_simulator simulator{};
	    const auto r = simulate_mign_function( spec, spec.outputs()[x].first, simulator);
		normal_MO.push_back(!r[0u]); 
	}
   
return exact_mig_abc (normal_MO, option, depth, fanout); 
}

std::vector<mign_graph> exact_mig_abc (std::vector<bool> normal_MO, unsigned option, int depth, int fanout)
{
  auto k = start;
  
  std::vector<mign_graph> mign; 
   
  while ( true )
  {  
     if ( verbose )
     {
		 std::cout << boost::format( "[i] check for realization with %d gates" ) % k << std::endl;
     }
  
	 if ( k > (13*normal_MO.size()))
	 {
		 std::cout << "Upper bound size reached" << std::endl;
		 return std::vector<mign_graph>();
	 }
	 
     auto inst = create_inst_MO (normal_MO);
     inst->create_var(k, depth, fanout); 
     int start_s=clock();
     inst->create_clauses(option);
	 
	 if ((fanout > 0) && (option == 0))
	 {
		for (auto h = 0u; h < k; h++)
		    inst->add_fanout(h);
	 } 
	 if ((fanout > 0) && (option == 1))
	 {
		for (auto h = 0u; h < k; h++)
		    inst->add_fanout(h);
	 } 
     int stop_s=clock();
	 if (verbose) 
	 {
		 std::cout << "All clauses runtime: " << (stop_s-start_s)/double(CLOCKS_PER_SEC) << std::endl;
	 }
	  
	 while (true)
	 {
	     start_s=clock();
	     auto result = inst->Sat_Solve(); 
		 stop_s=clock();
		 if (verbose)
		 {
			 std::cout << "SAT Solver runtime: " << (stop_s-start_s)/double(CLOCKS_PER_SEC) << std::endl;
		 }
		 
	     if ( result == 1)
	       {
		   std::cout << " SAT" << std::endl; 
	       mign = inst->extract_mig_MO( model_name, normal_MO, verbose );
		   if (option == 0)
		   {
			   return mign; 
		   }
		   else if (option == 2)
		   {
	  		   mign[0].compute_fanout(); 
	  		   auto node = check_fo (mign[0],fanout); 
	  		   if (node == -1)
	  		   {
	  			   	 return mign;
	  		   }
			   else 
			   {
	 			  inst->add_fanout(node); 
	 			  continue; 
			   }
		   }
		   else if ((option == 1) || (option == 3))
		   {
		   	  auto tt_mign_new = tt_simulate_MO(mign[0]); 
  		      if (inst->check(tt_mign_new) == false)
  		      {
  		   
  			   inst->add_more_clauses(tt_mign_new); 
  			   continue; 
		       }
			   else 
			   {
				   if (option == 1)
				   {
					   return mign; 
				   }
				   else 
					 {
			  		   mign[0].compute_fanout(); 
			  		   auto node = check_fo (mign[0],fanout); 
			  		   if (node == -1)
			  		   {
			  			   	 return mign;
			  		   }
					   else 
					   {
			 			  inst->add_fanout(node); 
			 			  continue; 
					   }
					 }  
			   }
		   }
	   }	   
	   else if ( result == 2 )
	      {
		  std::cout << " UNSAT" << std::endl; 
	      return std::vector<mign_graph>();
	      }
	   else
	      {
		     ++k;
		     break;
	      } 
	    } 
	 }
    
}

inline std::shared_ptr<exact_inst_cegar> create_inst_MO(std::vector<bool> normal_MO) const
{
  auto inst = std::make_shared<exact_inst_cegar>(spec.inputs().size(),verbose, spec.outputs().size()); 
  inst->tt_from_spec_MO( spec , normal_MO);
  return inst; 
}

private:
  mign_graph spec;
  unsigned start;
  int depth; 
  int fanout; 
  unsigned option;
  std::string model_name;
  bool all_solutions;
  boost::optional<unsigned> timeout;
  bool verbose;
};


boost::optional<mign_graph> exact_mig_with_sat_cegar(const mign_graph& spec, unsigned cegar_option, int depth, int fanout, const properties::ptr& settings,const properties::ptr& statistics)
{

  const auto all_solutions = get( settings, "all_solutions", false );

  c_exact_mig_abc_manager_MO mgr( spec , cegar_option, depth, fanout, settings, statistics );
  
  if ((cegar_option > 1) && (fanout < 0))
	 {
	 	std::cout << " Error. Cegar on fanout. Fanout value needs to be specified" << std::endl; 
		return boost::none;
	 } 
  
  auto start_s=clock();
  const auto migns = mgr.run();
  auto stop_s=clock();
  std::cout << "runtime: " << (stop_s-start_s)/double(CLOCKS_PER_SEC) << std::endl;
  
  if ( all_solutions )
  {
    set( statistics, "all_solutions", migns );
  }
  
  if ( migns.empty() )
  {
    return boost::none;
  }
  else
  {
    return migns.front();
  }

}

}

// Local Variables:
// c-basic-offset: 2
// eval: (c-set-offset 'substatement-open 0)
// eval: (c-set-offset 'innamespace 0)
// End:
