default: inductiveGraph

createBuildFolder:
	if not exist "./build" mkdir "./build"

inductiveGraph_agda: createBuildFolder
	@echo == Compiling inductiveGraph ==
	agda2hs -o ./build ./src/inductiveGraph.agda

inductiveGraph: inductiveGraph_agda
	stack ghc ./build/inductiveGraph.hs

patricia_agda: createBuildFolder
	@echo == Compiling PatriciaTree ==
	agda2hs -o ./build ./src/PatriciaTree.agda

patricia: patricia_agda
	stack ghc ./build/PatriciaTree.hs

common_agda: createBuildFolder
	@echo == Compiling CommonSubset ==
	agda2hs -o ./build ./src/CommonSubset.agda

common: common_agda
	stack ghc ./build/CommonSubset.hs

data_agda: createBuildFolder
	if not exist "./build/Data" mkdir "./build/Data"
	@echo == Compiling Data Library ==
	agda2hs -o ./build ./src/Data/List.agda
	agda2hs -o ./build ./src/Data/Maybe.agda

data: data_agda
	stack ghc ./build/Data/List.hs
	stack ghc ./build/Data/Maybe.hs

implicitField: createBuildFolder
	agda2hs -o ./build ./src/ImplicitFieldTest.agda
	stack ghc ./build/ImplicitFieldTest.hs