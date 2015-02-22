// (C) Copyright 2009 Eric Böse-Wolf <eric@boese-wolf.eu>,
// (C) Copyright 2010 Eric Wolf <eric@boese-wolf.eu>
//
// Boost Software License, Version 1.0 (See accompanying file
// LICENSE_1_0.txt or http://www.boost.org/LICENSE_1_0.txt)
// Distributed under the Boost Software License, Version 1.0.

#ifndef BOOST_GRAPH_TRANSITIVE_REDUCTION_HPP
#define BOOST_GRAPH_TRANSITIVE_REDUCTION_HPP

#include <vector>
#include <algorithm>
#include <functional>
#include <boost/bind.hpp>
#include <boost/iterator.hpp>
#include <boost/iterator/iterator_concepts.hpp>
#include <boost/graph/create_condensation_graph.hpp>
#include <boost/graph/vector_as_graph.hpp>
#include <boost/graph/strong_components.hpp>
#include <boost/graph/topological_sort.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/graph_concepts.hpp>
#include <boost/graph/named_function_params.hpp>
#include <boost/concept/requires.hpp>
#include <boost/mpl/or.hpp>
#include <boost/mpl/logical.hpp>
#ifdef DEBUG
#include <boost/graph/graph_utility.hpp>
#endif

namespace boost
{
 
    namespace detail
    {
        inline void
        union_successor_sets(const std::vector < std::size_t > &s1,
            const std::vector < std::size_t > &s2,
            std::vector < std::size_t > &s3)
        {
            BOOST_USING_STD_MIN();
            for (std::size_t k = 0; k < s1.size(); ++k)
                s3[k] = min BOOST_PREVENT_MACRO_SUBSTITUTION(s1[k], s2[k]);
        }
    }                             // namespace detail

    namespace detail
    {
        template < typename TheContainer, typename ST = std::size_t,
                   typename VT = typename TheContainer::value_type >
        struct subscript_t:public std::unary_function < ST, VT >
        {
            typedef VT& result_type;

            subscript_t(TheContainer & c):container(&c)
            {
            }
            VT & operator() (const ST & i) const
            {
                return (*container)[i];
            }
        protected:
            TheContainer * container;
        };
        template < typename TheContainer >
        subscript_t < TheContainer > subscript(TheContainer & c) {
            return subscript_t < TheContainer > (c);
        }
    } // namespace detail

    namespace detail
    {     
 
        //we directly head for avoiding partial specialization
        struct tr_compute_tr_tag {
            template < typename size_type >
            struct cg_data_store {       

                typedef size_type cg_vertex;
                typedef std::vector< std::vector< size_type > > cg_t;
                typedef typename cg_t::size_type size_t;

                cg_data_store( size_t n ) : cg_tr( n ) {}
                                
                void add_to_tr( cg_vertex u, cg_vertex v ) {
                    add_edge( u, v, cg_tr ); 
                }
                
                void add_to_tc( cg_vertex u, cg_vertex v ) {}
            
                cg_t cg_tr;               
            };
        };

        struct tr_compute_tc_tag {
            template < typename size_type >
            struct cg_data_store {       

                typedef size_type cg_vertex;
                typedef std::vector< std::vector< size_type > > cg_t;
                typedef typename cg_t::size_type size_t;

                cg_data_store( size_t n ) : cg_tc( n ) {}
                                
                void add_to_tr( cg_vertex u, cg_vertex v ) {}
                
                void add_to_tc( cg_vertex u, cg_vertex v ) {
                    add_edge( u, v, cg_tc );
                }
            
                cg_t cg_tc;               
            };
        };

        struct tr_compute_both_tag {
            template < typename size_type >
            struct cg_data_store {       

                typedef size_type cg_vertex;
                typedef std::vector< std::vector< size_type > > cg_t;
                typedef typename cg_t::size_type size_t;

                cg_data_store( size_t n ) : cg_tr( n ), cg_tc( n ) {}
                                
                void add_to_tr( cg_vertex u, cg_vertex v ) {
                    add_edge( u, v, cg_tr ); 
                }
                
                void add_to_tc( cg_vertex u, cg_vertex v ) {
                    add_edge( u, v, cg_tc );
                }
            
                cg_t cg_tr;               
                cg_t cg_tc;
            };
        };

        template < typename Graph, typename VertexIndexMap, typename Tag >
        struct minimal_solution_data {

            typedef Graph graph_type;
            typedef typename property_traits< VertexIndexMap >::value_type size_type;
            typedef typename std::vector< 
                std::vector< typename graph_traits< 
                                 Graph >::vertex_descriptor > > cl_type;

            typedef Tag tag;
            typedef typename Tag:: template cg_data_store< size_type >::cg_t cg_type;
            typedef typename Tag:: template cg_data_store< size_type >::cg_vertex cg_vertex;

            minimal_solution_data( Graph const & _g, 
                VertexIndexMap _index_map ) : g(_g), cg_data(num_vertices(g)),
                                              index_map(_index_map),
                                              component_number_vec(num_vertices(g)),
                                              component_number(&component_number_vec[0],
                                                  index_map),
                                              components() {}
            //compiler generated copy constructor and operator= should do well.

            void add_to_tc( cg_vertex u, cg_vertex v ) {
                cg_data.add_to_tc( u, v );
            }

            void add_to_tr( cg_vertex u, cg_vertex v ) {
                cg_data.add_to_tr( u, v );
            }


            Graph const & g;                                            //ORDER DEPENDENT
            typename Tag:: template cg_data_store< size_type > cg_data; //ORDER DEPENDENT
            VertexIndexMap index_map;                                   //ORDER DEPENDENT
            std::vector< size_type > component_number_vec;              //ORDER DEPENDENT
            iterator_property_map< size_type *, 
                                   VertexIndexMap, 
                                   size_type, 
                                   size_type & > component_number;      //ORDER DEPENDENT
            cl_type components;                                         //ORDER DEPENDENT

        };
    
        template < typename Graph, typename VertexIndexMap,
                   typename DataStore >
        // BOOST_CONCEPT_REQUIRES(
        //     ((VertexListGraphConcept< Graph >))
        //     ((IncidenceGraphConcept< Graph >))
        //     ((ReadablePropertyMapConcept< VertexIndexMapl,
        //                                   typename graph_traits<Graph>::vertex_descriptor >))
        //     ((Integer< typename property_traits<
        //             VertexIndexMap >::value_type >)),
        //     (void))

        void transitive_reduction_and_closure( const Graph& g,
            VertexIndexMap index_map,
            DataStore & d)
        {

            if (num_vertices(g) == 0)
                return;
            typedef typename graph_traits < Graph >::vertex_descriptor vertex;
            typedef typename graph_traits < Graph >::edge_descriptor edge;
            typedef typename graph_traits < Graph >::vertex_iterator vertex_iterator;
            typedef typename property_traits < VertexIndexMap >::value_type size_type;
            typedef typename graph_traits <
                Graph >::adjacency_iterator adjacency_iterator;

            typedef DataStore ds;

            typedef typename ds::cg_vertex cg_vertex;

            typename ds::size_type
                num_scc = strong_components(g, d.component_number,
                    vertex_index_map(index_map));

            build_component_lists(g, num_scc, d.component_number, d.components);

            typename ds::cg_type CG;

            create_condensation_graph(g, d.components, d.component_number, CG);

            std::vector<cg_vertex> topo_order;
            std::vector<size_type> topo_number(num_vertices(CG));
            topological_sort(CG, std::back_inserter(topo_order),
                vertex_index_map(identity_property_map()));
            std::reverse(topo_order.begin(), topo_order.end());
            size_type n = 0;
            for (typename std::vector<cg_vertex>::iterator iter = topo_order.begin();
                 iter != topo_order.end(); ++iter)
                topo_number[*iter] = n++;

            for (size_type i = 0; i < num_vertices(CG); ++i)
                std::sort(CG[i].begin(), CG[i].end(),
                    boost::bind(std::less<cg_vertex>(),
                        boost::bind(subscript(topo_number), _1),
                        boost::bind(subscript(topo_number), _2)));

            std::vector< std::vector< cg_vertex > > chains;
            {
                std::vector<size_type> in_a_chain(num_vertices(CG));
                for (typename std::vector<cg_vertex>::iterator i = topo_order.begin();
                     i != topo_order.end(); ++i) {
                    cg_vertex v = *i;
                    if (!in_a_chain[v]) {
                        chains.resize(chains.size() + 1);
                        std::vector<cg_vertex>& chain = chains.back();
                        for (;;) {
                            chain.push_back(v);
                            in_a_chain[v] = true;
                            typename graph_traits<typename ds::cg_type>::adjacency_iterator adj_first, adj_last;
                            boost::tie(adj_first, adj_last) = adjacent_vertices(v, CG);
                            typename graph_traits<typename ds::cg_type>::adjacency_iterator next
                                = std::find_if(adj_first, adj_last,
                                    std::not1(subscript(in_a_chain)));
                            if (next != adj_last)
                                v = *next;
                            else
                                break;            // end of chain, dead-end

                        }
                    }
                }
            }
            std::vector<size_type> chain_number(num_vertices(CG));
            std::vector<size_type> pos_in_chain(num_vertices(CG));
            for (size_type i = 0; i < chains.size(); ++i)
                for (size_type j = 0; j < chains[i].size(); ++j) {
                    cg_vertex v = chains[i][j];
                    chain_number[v] = i;
                    pos_in_chain[v] = j;
                }

            size_type inf = (std::numeric_limits< size_type >::max)();
            std::vector<std::vector<size_type> > successors(num_vertices(CG),
                std::vector<size_type>
                (chains.size(), inf));

            for (typename std::vector<cg_vertex>::reverse_iterator
                     i = topo_order.rbegin(); i != topo_order.rend(); ++i) {
                cg_vertex u = *i;
                typename graph_traits<typename ds::cg_type >::adjacency_iterator adj, adj_last;
                for (boost::tie(adj, adj_last) = adjacent_vertices(u, CG);
                     adj != adj_last; ++adj) {
                    cg_vertex v = *adj;
                    if (topo_number[v] < successors[u][chain_number[v]]) {
                        // Succ(u) = Succ(u) U Succ(v)
                        union_successor_sets(successors[u], successors[v],
                            successors[u]);
                        // Succ(u) = Succ(u) U {v}
                        successors[u][chain_number[v]] = topo_number[v];
                        if( mpl::or_< is_same< typename ds::tag, tr_compute_tr_tag >,
                                 is_same< typename ds::tag, tr_compute_both_tag >
                            >::value )  
                            d.add_to_tr( u, v );                    
                    }
                }
            }

            //constuct the transitive closure of the condensation graph.
            if( mpl::or_< is_same< typename ds::tag, tr_compute_tc_tag >,
                     is_same< typename ds::tag, tr_compute_both_tag > 
                >::value ) {
                for (size_type i = 0; i < num_scc; ++i)
                    for (size_type j = 0; j < chains.size(); ++j) {
                        size_type topo_num = successors[i][j];
                        if (topo_num < inf) {
                            cg_vertex v = topo_order[topo_num];
                            for (size_type k = pos_in_chain[v]; k < chains[j].size(); ++k)
                                d.add_to_tc( i, chains[j][k] );
                        }
                    }
            }
        
        }

        template< typename DataStore, typename Functionoid > 
        void construct_transitive_closure( Functionoid f, 
            DataStore msd ) 
        {
            typedef typename DataStore::cg_vertex cg_vertex;
            typedef typename DataStore::size_type size_type;

            // Add edges between all the vertices in two adjacent SCCs
            typename graph_traits< typename DataStore::cg_type >::vertex_iterator si, si_end;
            for (boost::tie(si, si_end) = vertices(msd.cg_data.cg_tc); si != si_end; ++si) {
                cg_vertex s = *si;
                typename graph_traits< typename DataStore::cg_type >::adjacency_iterator i, i_end;
                for (boost::tie(i, i_end) = adjacent_vertices(s, msd.cg_data.cg_tc); i != i_end; ++i) {
                    cg_vertex t = *i;
                    for (size_type k = 0; k < msd.components[s].size(); ++k)
                        for (size_type l = 0; l < msd.components[t].size(); ++l)
                            f(msd.components[s][k], msd.components[t][l]);
                }
            }

            // Add edges connecting all vertices in a SCC
            for (size_type i = 0; i < msd.components.size(); ++i)
                if (msd.components[i].size() > 1)
                    for (size_type k = 0; k < msd.components[i].size(); ++k)
                        for (size_type l = 0; l < msd.components[i].size(); ++l) {
                            f( msd.components[i][k], msd.components[i][l]);
                        }
        
            add_loops( f, msd );
        }

        template < typename DataStore, typename Functionoid >
        void add_loops( Functionoid f, 
            DataStore msd )
        {
            typedef typename graph_traits< 
                typename DataStore::graph_type >::vertex_iterator vertex_iterator;
            typedef typename graph_traits< 
                typename DataStore::graph_type >::adjacency_iterator adjacency_iterator;
            // Find loopbacks in the original graph.
            // Need to add it to transitive closure.

            vertex_iterator i, i_end;
            for (boost::tie(i, i_end) = vertices(msd.g); i != i_end; ++i)
                {
                    adjacency_iterator ab, ae;
                    for (boost::tie(ab, ae) = adjacent_vertices(*i, msd.g); ab != ae; ++ab)
                        {
                            if (*ab == *i)
                                if (msd.components[msd.component_number[*i]].size() == 1)
                                    f(*i,*i );
                        }
                }
        }
        
        template < typename OutputIterator, 
                   typename VertexDescriptor, 
                   typename VertexIndexMap >
        class output_iterator_functionoid {
        private:
            OutputIterator iter;
            VertexIndexMap index_map;
            typedef typename property_traits< VertexIndexMap >::value_type size_type;
        public:
            output_iterator_functionoid( OutputIterator _iter, 
                VertexIndexMap _index_map ) 
                : iter( _iter ), index_map( _index_map ) {}
            void operator()( VertexDescriptor u, VertexDescriptor v )
            {
                *iter = std::pair< size_type, size_type >(
                    index_map[ u ], index_map[ v ] );
            }
        };

        template < typename Graph,
                   typename GraphOut,
                   typename G_to_GO_Vertex_Map >
        class write_to_mutable_graph_functionoid {
        private:
            GraphOut & go;
            G_to_GO_Vertex_Map g_to_go_map;
            typedef typename graph_traits< Graph >::vertex_descriptor 
            vertex_descriptor;
        public:
            write_to_mutable_graph_functionoid( Graph const & g,
                GraphOut & _go, G_to_GO_Vertex_Map _g_to_go_map )
                : go( _go ), g_to_go_map( _g_to_go_map ) {

                typedef typename graph_traits< Graph >::vertex_iterator
                    vertex_iterator;

                vertex_iterator va,ve;
                for( tie(va,ve) = vertices( g ); va != ve; ++va ) {
                    g_to_go_map[ *va ] = add_vertex( go );
                }
            }

            void operator()( vertex_descriptor u, vertex_descriptor v )
            {
                add_edge( g_to_go_map[u], g_to_go_map[v], go );
            }
        };

        template < typename DataStore, typename Functionoid >
        void construct_transitive_reduction( Functionoid f, DataStore msd )
        {
            
            typedef typename graph_traits< 
                typename DataStore::cg_type >::vertex_iterator vertex_iterator;
            typedef typename graph_traits< 
                typename DataStore::cg_type >::adjacency_iterator adjacency_iterator;
            typedef typename DataStore::size_type size_type;

            //first process the relevant edges of the transitive reduction 
            //of the condensation graph
            {
                vertex_iterator i, i_end;
                for( tie(i,i_end) = vertices( msd.cg_data.cg_tr ); 
                     i != i_end;
                     ++i ) {
                    adjacency_iterator a, a_end;
                    for( tie(a, a_end ) = adjacent_vertices( *i, msd.cg_data.cg_tr );
                         a != a_end;
                         ++a ) {
                        f(msd.components[*i][0],
                            msd.components[*a][0]);
                    }
                }
            }
        
        
            //then we stream a circle for each strong component
            {
                for(size_type act_comp = 0;
                    act_comp != msd.components.size();
                    ++act_comp ) {
                    if( msd.components[ act_comp ].size() > 1 )
                        for( size_type act_vertex = 0;
                             act_vertex != msd.components[ act_comp ].size();
                             ++act_vertex ) {
                            if( (act_vertex + 1) != msd.components[ act_comp ].size() ) {
                                f(msd.components[act_comp][act_vertex],
                                    msd.components[act_comp][act_vertex + 1]);
                            } else {
                                f(msd.components[act_comp][act_vertex],
                                    msd.components[act_comp][0]);
                            }
                        }
                }
            }
            
            add_loops( f, msd );
        }        
    
    } //namespace detail;

    template < typename Graph, 
               typename OutputIterator,
               typename VertexIndexMap >
    void transitive_reduction_stream(Graph const & g,
        OutputIterator out,
        VertexIndexMap index_map)
    {
        detail::minimal_solution_data<Graph, VertexIndexMap, detail::tr_compute_tr_tag>
            msd( g, index_map );

        detail::transitive_reduction_and_closure(g, index_map, msd);

        detail::output_iterator_functionoid<OutputIterator, 
                                            typename graph_traits< Graph >::vertex_descriptor, 
                                            VertexIndexMap> f(out, index_map);
    
        detail::construct_transitive_reduction(f, msd);
    }

    template < typename Graph, 
               typename OutputIterator,
               typename VertexIndexMap >
    void transitive_closure_stream(Graph const & g,
        OutputIterator out,
        VertexIndexMap index_map)
    {
        detail::minimal_solution_data<Graph, VertexIndexMap, detail::tr_compute_tc_tag>
            msd( g, index_map );
        
        detail::transitive_reduction_and_closure(g, index_map, msd);
        
        detail::output_iterator_functionoid<OutputIterator, 
                                            typename graph_traits< Graph >::vertex_descriptor, 
                                            VertexIndexMap> f(out, index_map);
    
        detail::construct_transitive_closure(f, msd);
    }

    template < typename Graph, 
               typename OutputIterator1,
               typename OutputIterator2,
               typename VertexIndexMap >
    void transitive_reduction_and_closure_stream(Graph const & g,
        OutputIterator1 out_tr,
        OutputIterator2 out_tc,
        VertexIndexMap index_map)
    {
        detail::minimal_solution_data<Graph, VertexIndexMap, detail::tr_compute_both_tag>
            msd( g, index_map );
        
        detail::transitive_reduction_and_closure(g, index_map, msd);
        
        detail::output_iterator_functionoid<OutputIterator1, 
                                            typename graph_traits< Graph >::vertex_descriptor, 
                                            VertexIndexMap> f1(out_tr, index_map);
    
        detail::construct_transitive_reduction(f1, msd);
    
        detail::output_iterator_functionoid<OutputIterator2, 
                                        typename graph_traits< Graph >::vertex_descriptor, 
                                        VertexIndexMap> f2(out_tc, index_map);

        detail::construct_transitive_closure(f2, msd);
    }

    template < typename Graph, 
               typename GraphTC,
               typename G_to_TC_VertexMap,
               typename GraphTR,
               typename G_to_TR_VertexMap,
               typename VertexIndexMap >
    void transitive_reduction_and_closure_mutgr(Graph const & g,
        GraphTC & tc,
        G_to_TC_VertexMap g_to_tc_map,
        GraphTR & tr,
        G_to_TR_VertexMap g_to_tr_map,
        VertexIndexMap index_map)
    {
        detail::minimal_solution_data<Graph, VertexIndexMap, detail::tr_compute_both_tag>
            msd( g, index_map );
        
        detail::transitive_reduction_and_closure(g, index_map, msd);

        detail::write_to_mutable_graph_functionoid< Graph, GraphTR, G_to_TR_VertexMap >
            f1(g, tr, g_to_tr_map);
    
        detail::construct_transitive_reduction(f1, msd);

        detail::write_to_mutable_graph_functionoid< Graph, GraphTC, G_to_TC_VertexMap >
            f2(g, tc, g_to_tc_map);
    
        detail::construct_transitive_closure(f2, msd);
    }

    template < typename Graph, 
               typename GraphTC,
               typename G_to_TC_VertexMap,
               typename VertexIndexMap >
    void transitive_closure_mutgr(Graph const & g,
        GraphTC & tc,
        G_to_TC_VertexMap g_to_tc_map,
        VertexIndexMap index_map)
    {
        detail::minimal_solution_data<Graph, VertexIndexMap, detail::tr_compute_tc_tag>
            msd( g, index_map );
        
        detail::transitive_reduction_and_closure(g, index_map, msd);

        detail::write_to_mutable_graph_functionoid< Graph, GraphTC, G_to_TC_VertexMap >
            f2(g, tc, g_to_tc_map);
    
        detail::construct_transitive_closure(f2, msd);
    }

    template < typename Graph, 
               typename GraphTR,
               typename G_to_TR_VertexMap,
               typename VertexIndexMap >
    void transitive_reduction_mutgr(Graph const & g,
        GraphTR & tr,
        G_to_TR_VertexMap g_to_tr_map,
        VertexIndexMap index_map)
    {
        detail::minimal_solution_data<Graph, VertexIndexMap, detail::tr_compute_tr_tag>
            msd( g, index_map );
        
        detail::transitive_reduction_and_closure(g, index_map, msd);

        detail::write_to_mutable_graph_functionoid< Graph, GraphTR, G_to_TR_VertexMap >
            f1(g, tr, g_to_tr_map);
    
        detail::construct_transitive_reduction(f1, msd);
    }


} //namespace boost;

#endif //BOOST_GRAPH_TRANSITIVE_REDUCTION_HPP








        
