import {createApp} from 'vue'
import './style.css'
import App from './App.vue'
import PrimeVue from 'primevue/config';
import Aura from '@primevue/themes/aura';
import {Button, Message, Select, Toast, ToastService} from "primevue";
import {Form} from "@primevue/forms";

const app = createApp(App)

app.use(PrimeVue, {
  theme: {
    preset: Aura
  }
});
app.use(ToastService);

app.component('Button', Button);
app.component('Form', Form);
app.component('Message', Message);
app.component('Select', Select);
app.component('Toast', Toast);

app.mount('#app');
