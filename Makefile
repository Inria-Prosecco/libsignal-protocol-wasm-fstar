vanilla:
	sed \
		-e 's|{{{PLACEHOLDER}}}|<script type="text/javascript" src="../src/SignalCore.js" data-cover-never></script>|' \
	  test/index.html.proto \
		 > test/index.html

fstar:
	make -C fstar compile-wasm
	sed -e 's|{{{PLACEHOLDER}}}| \
	  <script type="text/javascript" src="../fstar/signal-wasm/shell.js" data-cover-never></script> \
	  <script type="text/javascript" src="../fstar/signal-wasm/loader.js" data-cover-never></script> \
	  <script type="text/javascript" src="../src/SignalCoreWasm.js" data-cover-never></script>|' \
	  test/index.html.proto \
		 > test/index.html

update-demo:
	cp -f src/*.js demo/
	cp -f fstar/signal-wasm/*.wasm demo/
	cp -f fstar/signal-wasm/loader.js demo/
	cp -f fstar/signal-wasm/shell.js demo/
