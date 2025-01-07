<script setup>
import {onMounted, ref} from 'vue';
import {ConsoleStdout, WASI} from "@bjorn3/browser_wasi_shim";

const algorithms = ref(null);
const selectedAlgorithm = ref(null);
const autoFilteredAlg = ref([]);

const selectButtonValue = ref({ name: 'Paper' });
const selectButtonValues = ref([{ name: 'Paper' }, { name: 'Extended' }]);

const examples = ref(null);
const selectedExample = ref(null);
const autoFilteredEx = ref([]);

const code = ref('');
const output = ref('');
const loading = ref(false);

let wasmModule = null;
const outputBuffer = ref('');

async function loadWasmModule() {
    if (!wasmModule) {
        try {
            const response = await fetch('/bin.wasm');
            const bytes = await response.arrayBuffer();
            wasmModule = await WebAssembly.compile(bytes);
        } catch (error) {
            console.error('WASM module loading failed:', error);
            output.value = `WASM module loading failed: ${error.message}`;
        }
    }
}

async function runWasm(args) {
    loading.value = true;
    output.value = '';

    try {
        await loadWasmModule();

        const env = [];
        const fds = [
            null, // stdin
            ConsoleStdout.lineBuffered((msg) => {
                outputBuffer.value += `${msg}\n`;
            }),
        ];

        const wasi = new WASI(args, env, fds);
        const instance = await WebAssembly.instantiate(wasmModule, {
            wasi_snapshot_preview1: wasi.wasiImport,
        });

        wasi.start(instance);
        output.value = outputBuffer.value;
        outputBuffer.value = '';
    } catch (error) {
        console.error('error running WASM:', error);
        output.value = `error running WASM: ${error.message}`;
    } finally {
        loading.value = false;
    }
}

function infer() {
    if (!selectedAlgorithm.value || !selectedAlgorithm.value.code) {
        output.value = 'Please select an algorithm';
        return;
    }

    const currentCode = code.value;
    const args = generateArgs(selectedAlgorithm.value.code, currentCode);
    runWasm(args);
}

function generateArgs(algorithmCode, inputCode) {
    switch (algorithmCode) {
        default:
            return ['infer', '--alg', algorithmCode, inputCode];
    }
}

onMounted(() => {
    algorithms.value = [
        { name: 'Algorithm W', code: 'W' },
        { name: 'Complete and Easy Bidirectional Typechecking for Higher-rank Polymorphism', code: 'DK' },
        { name: 'A Mechanical Formalization of Higher-Ranked Polymorphic Type Inference', code: 'Worklist' },
        { name: 'Elementary Type Inference', code: 'Elementary' },
        { name: 'Fully Grounding Type Inference for the HDM System', code: 'R' },
        { name: 'Greedy Implicit Bounded Quantification', code: 'Bounded' },
        { name: 'Contextual Typing', code: 'Contextual' },
        { name: 'Bidirectional Higher-Rank Polymorphism with Intersection and Union Types', code: 'IU' }
    ];
    examples.value = [
        { name: 'trivial application', code: '(\\x. x) 1' },
        { name: 'let', code: 'let id = \\x. x in id 1' },
        { name: 'let-polymorphism', code: 'let id = \\x. x in (id 1, id True)' },
        { name: 'higher-rank', code: '(\\f. \\x. f x) : (forall a. a -> a) -> Int -> Int' },
        { name: 'higher-rank bounded', code: '(\\f. \\x. f x) : (forall (a <: Int). a -> a) -> Int -> Int' },
        { name: 'explicit type application', code: '(/\\a. (\\x. x) : a -> a) @ (forall a. a -> a)' },
        { name: 'intersection types', code: '(\\f. f True) : ((Int -> Int) & (Bool -> Bool)) -> Bool' },
    ];
});

function searchAlgorithm(event) {
    if (!event.query.trim().length) {
        autoFilteredAlg.value = [...algorithms.value];
    } else {
        autoFilteredAlg.value = algorithms.value.filter((alg) => {
            return alg.name.toLowerCase().startsWith(event.query.toLowerCase());
        });
    }
}

function searchExample(event) {
    if (!event.query.trim().length) {
        autoFilteredEx.value = [...examples.value];
    } else {
        autoFilteredEx.value = examples.value.filter((ex) => {
            return ex.name.toLowerCase().startsWith(event.query.toLowerCase());
        });
    }
}

function handleExampleSelect(event) {
  const selected = event.value;
  if (selected && selected.code) {
    code.value = selected.code;
  }
}

function handleCodeChange(event) {
  code.value = event.target.value;
  selectedExample.value = null;
}
</script>


<div class="flex flex-col gap-2 mb-4">
    <label>Type Inference Algorithm</label>
    <AutoComplete v-model="selectedAlgorithm" :suggestions="autoFilteredAlg" optionLabel="name"
        placeholder="Select Algorithm" dropdown display="chip" @complete="searchAlgorithm($event)" />
</div>

<div class="flex flex-col gap-2 mb-2">
    <label>Example Program</label>
    <div class="flex flex-wrap justify-between items-start gap-4 mb-4">
        <AutoComplete v-model="selectedExample" :suggestions="autoFilteredEx" display="chip"
                      dropdown optionLabel="name" placeholder="(Optional) Load Example"
                      @complete="searchExample($event)"
                      @option-select="handleExampleSelect"/>
    </div>
</div>

<div class="flex flex-col gap-2 mb-4">
    <label>Input Program</label>
    <Textarea v-model="code" class="code" rows="2" spellcheck="false" @input="handleCodeChange"/>
    <div class="flex justify-end mb-4">
        <Button :loading="loading" icon="pi pi-caret-right" label="Infer" type="button" @click="infer"/>
    </div>
</div>

<div class="flex flex-col gap-2 mb-4">
    <label>Inference Output</label>
    <pre class="output">{{ output }}</pre>
</div>
