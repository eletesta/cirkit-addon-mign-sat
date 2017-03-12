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

/**
 * @file mign.hpp
 *
 * @brief New approach for MIG- exact synthesis Based on Knuth The Art of COmputer Programming 6
 *
 * @author Eleonora Testa
 * @since  2.3
 */

#ifndef MIG_SAT_HPP
#define MIG_SAT_HPP

#include <boost/optional.hpp>

#include <core/properties.hpp>

#include <classical/mign/mign.hpp>
#include <classical/utils/truth_table_utils.hpp>

namespace cirkit
{ 
	void exact_mig_sat (); 
	boost::optional<mign_graph> exact_mig_with_sat_abc( const mign_graph& spec, const properties::ptr& settings,const properties::ptr& statistics ); 
	boost::optional<mign_graph> exact_mig_with_sat_abc_MO( const mign_graph& spec, const properties::ptr& settings,const properties::ptr& statistics ); 
    boost::optional<mign_graph> exact_mig_with_sat_abc(const tt& spec, const properties::ptr& settings, const properties::ptr& statistics );											   
												 
}

#endif

// Local Variables:
// c-basic-offset: 2
// eval: (c-set-offset 'substatement-open 0)
// eval: (c-set-offset 'innamespace 0)
// End:
